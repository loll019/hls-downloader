"""
HLS Video Downloader - interfaccia grafica.

Avvio:  python hls_downloader.py

Si apre una finestra in cui indicare l'URL della pagina del video, il nome del
file MP4 e la cartella di destinazione. Prima di connettersi viene verificato
che sia attiva una VPN; il flusso HLS viene poi intercettato aprendo la pagina
nel browser predefinito (tramite Playwright): i segmenti vengono scaricati in parallelo su
connessioni persistenti, decifrati e infine uniti in un MP4 con FFmpeg.

Dipendenze:  python -m pip install playwright customtkinter pycryptodome
"""
from __future__ import annotations

import asyncio
import base64
import functools
import glob
import http.client
import json
import os
import queue
import re
import shutil
import socket
import ssl
import subprocess
import sys
import threading
import time
import tkinter as tk
import urllib.parse
import urllib.request
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor
from concurrent.futures import wait as wait_futures
from datetime import datetime, timedelta
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

# Librerie esterne necessarie: modulo da importare -> pacchetto da installare con pip
REQUIRED_PACKAGES = {
    "customtkinter": "customtkinter",  # Interfaccia grafica
    "playwright": "playwright",  # Controllo del browser
    "Crypto": "pycryptodome",  # Decifratura dei segmenti AES-128
}

ctk = async_playwright = AES = None


def load_optional_modules():
    """Importa le librerie esterne; quelle mancanti restano None e vengono segnalate all'utente."""
    global ctk, async_playwright, AES
    try:
        import customtkinter as ctk
    except ImportError:
        ctk = None
    try:
        from playwright.async_api import async_playwright
    except ImportError:
        async_playwright = None
    try:
        from Crypto.Cipher import AES
    except ImportError:
        AES = None


load_optional_modules()

# ============================================================
# CONFIGURAZIONE
# ============================================================
TIMEOUT_PLAYWRIGHT = 60  # Attesa massima per l'intercettazione del flusso (secondi)
MIN_MAIN_DURATION = 300  # Flussi più brevi (secondi) sono considerati pubblicità finché non c'è di meglio

# WebRTC disattivato nel browser aperto dall'app: le pagine non possono usarlo per scoprire gli indirizzi
# di rete del PC né aprire connessioni dirette fuori dalla VPN. I player HLS non ne hanno bisogno.
BROWSER_ARGS = [
    "--disable-blink-features=AutomationControlled",
    "--force-webrtc-ip-handling-policy=disable_non_proxied_udp",  # Niente UDP diretto fuori dalla VPN
    "--incognito",  # Finestra in incognito: niente cronologia, cookie o cache salvati
    "--block-new-web-contents",  # Blocca a monte le nuove finestre/schede (i popunder pubblicitari)
    "--disable-features=Translate,InterestCohort",
]
WEBRTC_BLOCK_SCRIPT = """
(() => {
    for (const name of ['RTCPeerConnection', 'webkitRTCPeerConnection', 'RTCDataChannel',
                        'RTCIceCandidate', 'RTCSessionDescription', 'RTCRtpSender', 'RTCRtpReceiver']) {
        try { Object.defineProperty(window, name, {value: undefined, writable: false, configurable: false}); }
        catch (e) {}
    }
})();
"""
# Neutralizza i trucchi con cui le pubblicità aprono pop-up o dirottano la pagina del player:
# window.open non apre nulla, e i gestori "stai per uscire" non possono bloccare o far ricaricare la pagina.
POPUP_BLOCK_SCRIPT = """
(() => {
    try { window.open = () => null; } catch (e) {}
    for (const name of ['onbeforeunload', 'onunload']) {
        try { Object.defineProperty(window, name, {get: () => null, set: () => {}, configurable: false}); }
        catch (e) {}
    }
    const realAdd = window.EventTarget && EventTarget.prototype.addEventListener;
    if (realAdd) {
        EventTarget.prototype.addEventListener = function (type, listener, options) {
            if (type === 'beforeunload' || type === 'unload') return;  // ignora i blocchi d'uscita
            return realAdd.call(this, type, listener, options);
        };
    }
})();
"""
SETTINGS_FILE = Path.home() / ".hls_downloader.json"  # Ricorda cartella ed eventuale browser scelto a mano
# Servizi per leggere l'IP pubblico, provati in ordine: se uno è bloccato (es. dal blocco tracker/pubblicità
# della VPN, come NetShield di Proton) si passa al successivo. Solo ip-api.com segnala anche VPN e datacenter.
IP_CHECK_SERVICES = (
    ("ip-api", "http://ip-api.com/json/?fields=status,message,query,country,isp,proxy,hosting"),
    ("ipwhois", "https://ipwho.is/"),
    ("ipinfo", "https://ipinfo.io/json"),
    ("ipify", "https://api.ipify.org?format=json"),
)
# Provider tipici di VPN e datacenter: con i servizi che non lo segnalano, l'IP si considera «di una VPN»
DATACENTER_HINTS = (
    "proton", "worldstream", "m247", "datacamp", "hosting", "data center", "datacenter", "cloud", "ovh",
    "hetzner", "digitalocean", "leaseweb", "choopa", "vultr", "amazon", "google", "microsoft", "akamai",
    "linode", "mullvad", "nord", "surfshark", "clouvider", "xtom", "zenlayer", "packethub", "contabo", "server",
)
RATE_WINDOW = 10  # Secondi usati per calcolare velocità e tempo rimanente
MAX_RESUME_ATTEMPTS = 3  # Riprese consecutive senza progressi prima di arrendersi
# Oltre questo numero di pezzi (somma di tutte le tracce) non si usa «concatf», che li apre tutti insieme:
# Windows consente circa 8000 file aperti, e un film di 4 ore con video e due audio ne ha più di 10000.
CONCATF_MAX_FILES = 3000
SEGMENT_WORKERS = 8  # Connessioni contemporanee predefinite (modificabili dalla finestra)
WORKER_CHOICES = ("4", "8", "12", "16")
SEGMENT_RETRIES = 5  # Tentativi per segmento in caso di errori di rete
HTTP_TIMEOUT = 20  # Secondi di attesa massima per una risposta del server
MAX_REDIRECTS = 5
STATE_SAVE_INTERVAL = 5  # Ogni quanti secondi viene aggiornato stato.json durante il download
# ============================================================

APP_TITLE = "HLS Downloader"
NO_WINDOW = subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0

# Parole chiave delle schede di rete create dai client VPN più diffusi (Windows)
VPN_ADAPTER_KEYWORDS = (
    "vpn", "wireguard", "wintun", "tap-windows", "openvpn", "nordlynx", "proton",
    "mullvad", "surfshark", "cyberghost", "private internet access", "windscribe",
    "hotspot shield", "tunnelbear", "anyconnect", "globalprotect", "pangp", "fortinet",
)
# Prefissi delle interfacce VPN su Linux/macOS
VPN_INTERFACE_PREFIXES = ("tun", "tap", "wg", "ppp", "nordlynx", "proton", "mullvad")

LANGUAGE_CODES = {  # ISO 639-1 -> ISO 639-2, usato nei metadati dell'MP4
    "it": "ita", "en": "eng", "ja": "jpn", "es": "spa", "fr": "fra", "de": "deu", "pt": "por", "ru": "rus",
    "zh": "zho", "ko": "kor", "ar": "ara", "nl": "nld", "pl": "pol", "tr": "tur", "sv": "swe", "hi": "hin",
}

# ============================================================
# TEMA GRAFICO
# ============================================================
FONT = "Segoe UI" if sys.platform == "win32" else "Helvetica"
MONO = "Consolas" if sys.platform == "win32" else "Courier"

BG = "#0d0f14"
CARD = "#151821"
CARD_BORDER = "#232838"
INPUT = "#0f1117"
TILE = "#10131a"
SURFACE = "#1d2130"
SURFACE_HOVER = "#272c3d"
TEXT = "#e7e9ef"
MUTED = "#8a92a6"
FAINT = "#5d6478"
ACCENT = "#7c5cff"
ACCENT_HOVER = "#6847f5"
ACCENT_LIGHT = "#a28cff"
ACCENT_DIM = "#3b3266"
SUCCESS = "#22c55e"
SUCCESS_DARK = "#16a34a"
WARNING_DARK = "#d97706"
DANGER = "#ef4444"
DANGER_DARK = "#dc2626"

PILL_STYLES = {  # stato: (sfondo, testo)
    "ok": ("#11291b", "#4ade80"),
    "warn": ("#2e2410", "#fbbf24"),
    "error": ("#2f1316", "#f87171"),
    "pending": (SURFACE, "#9aa3b5"),
}
STEP_STYLES = {  # stato: (cerchio, testo)
    "pending": (SURFACE, MUTED),
    "active": (ACCENT, "#ffffff"),
    "done": (SUCCESS_DARK, "#ffffff"),
    "warn": (WARNING_DARK, "#ffffff"),
    "error": (DANGER_DARK, "#ffffff"),
}


# ============================================================
# LINGUE DELL'INTERFACCIA
# ============================================================
LANGUAGES = {"it": "Italiano", "en": "English", "es": "Español", "fr": "Français", "ja": "日本語"}
_LANGUAGE_INDEX = {code: i for i, code in enumerate(LANGUAGES)}
_language = "it"

TEXTS = {
    # --- Finestra principale ---
    "header_subtitle": (
        "Incolla il link della pagina, scegli nome e cartella, premi Scarica.",
        "Paste the page link, choose a name and folder, press Download.",
        "Pega el enlace de la página, elige nombre y carpeta y pulsa Descargar.",
        "Collez le lien de la page, choisissez un nom et un dossier, puis cliquez sur Télécharger.",
        "ページのリンクを貼り付け、名前と保存先を選んで「ダウンロード」を押してください。"),
    "language_label": ("🌐  Lingua", "🌐  Language", "🌐  Idioma", "🌐  Langue", "🌐  言語"),
    "card_video": ("VIDEO", "VIDEO", "VÍDEO", "VIDÉO", "動画"),
    "field_url": ("URL della pagina", "Page URL", "URL de la página", "URL de la page", "ページのURL"),
    "placeholder_url": ("https://…", "https://…", "https://…", "https://…", "https://…"),
    "btn_paste": ("Incolla", "Paste", "Pegar", "Coller", "貼り付け"),
    "field_name": ("Nome del file", "File name", "Nombre del archivo", "Nom du fichier", "ファイル名"),
    "default_file_name": ("video_scaricato", "downloaded_video", "video_descargado", "video_telechargee",
                          "ダウンロード動画"),
    "placeholder_name": ("nome del video", "video name", "nombre del vídeo", "nom de la vidéo", "動画の名前"),
    "field_folder": ("Salva in", "Save to", "Guardar en", "Enregistrer dans", "保存先"),
    "placeholder_folder": ("cartella di destinazione", "destination folder", "carpeta de destino",
                           "dossier de destination", "保存先フォルダー"),
    "btn_browse": ("Sfoglia…", "Browse…", "Examinar…", "Parcourir…", "参照…"),
    "btn_download": ("⬇   Scarica", "⬇   Download", "⬇   Descargar", "⬇   Télécharger", "⬇   ダウンロード"),
    "btn_add_queue": ("＋   Aggiungi alla coda", "＋   Add to queue", "＋   Añadir a la cola",
                      "＋   Ajouter à la file", "＋   キューに追加"),
    "card_checks": ("CONTROLLI", "CHECKS", "COMPROBACIONES", "VÉRIFICATIONS", "チェック"),
    "check_vpn": ("VPN", "VPN", "VPN", "VPN", "VPN"),
    "check_browser": ("Browser", "Browser", "Navegador", "Navigateur", "ブラウザー"),
    "check_ffmpeg": ("FFmpeg", "FFmpeg", "FFmpeg", "FFmpeg", "FFmpeg"),
    "check_speed": ("Velocità", "Speed", "Velocidad", "Vitesse", "速度"),
    "speed_hint": (
        "Connessioni in parallelo: più sono, più il download è veloce. Se compaiono errori o rallentamenti, scegline meno.",
        "Parallel connections: the more you use, the faster the download. If errors or slowdowns appear, choose fewer.",
        "Conexiones en paralelo: cuantas más, más rápida es la descarga. Si aparecen errores o lentitud, elige menos.",
        "Connexions en parallèle : plus il y en a, plus le téléchargement est rapide. En cas d'erreurs ou de "
        "ralentissements, choisissez-en moins.",
        "同時接続数：多いほど高速になります。エラーや速度低下が起きる場合は減らしてください。"),
    "btn_recheck": ("↻  Ricontrolla", "↻  Check again", "↻  Comprobar", "↻  Revérifier", "↻  再確認"),
    "btn_change": ("Cambia…", "Change…", "Cambiar…", "Changer…", "変更…"),
    "btn_use_default": ("Usa predefinito", "Use default", "Usar predeterminado", "Par défaut", "既定に戻す"),
    "card_download": ("DOWNLOAD", "DOWNLOAD", "DESCARGA", "TÉLÉCHARGEMENT", "ダウンロード"),
    "tile_size": ("Scaricato", "Downloaded", "Descargado", "Téléchargé", "ダウンロード済み"),
    "tile_speed": ("Velocità", "Speed", "Velocidad", "Vitesse", "速度"),
    "tile_eta": ("Tempo rimanente", "Time left", "Tiempo restante", "Temps restant", "残り時間"),
    "tile_position": ("Video", "Video", "Vídeo", "Vidéo", "動画"),
    "tile_calculating": ("calcolo…", "calculating…", "calculando…", "calcul…", "計算中…"),
    "tile_paused": ("in pausa", "paused", "en pausa", "en pause", "一時停止中"),
    "tile_almost_done": ("quasi finito", "almost done", "casi listo", "presque fini", "まもなく完了"),
    "tile_finished": ("Finito", "Finished", "Terminado", "Terminé", "完了"),
    "btn_cancel": ("✕   Annulla", "✕   Cancel", "✕   Cancelar", "✕   Annuler", "✕   キャンセル"),
    "btn_open_folder": ("Apri cartella", "Open folder", "Abrir carpeta", "Ouvrir le dossier", "フォルダーを開く"),
    "step_vpn": ("VPN", "VPN", "VPN", "VPN", "VPN"),
    "step_browser": ("Browser", "Browser", "Navegador", "Navigateur", "ブラウザー"),
    "step_download": ("Download", "Download", "Descarga", "Téléchargement", "ダウンロード"),
    "step_mp4": ("File MP4", "MP4 file", "Archivo MP4", "Fichier MP4", "MP4ファイル"),
    "raw": ("{text}", "{text}", "{text}", "{text}", "{text}"),

    # --- Coda ---
    "tab_queue": ("Coda ({n})", "Queue ({n})", "Cola ({n})", "File d'attente ({n})", "キュー ({n})"),
    "tab_log": ("Registro", "Log", "Registro", "Journal", "ログ"),
    "queue_empty": (
        "La coda è vuota. Durante un download compila link, nome e cartella e premi «Aggiungi alla coda»: "
        "i video partiranno uno dopo l'altro.",
        "The queue is empty. While a download is running, fill in link, name and folder and press "
        "\"Add to queue\": the videos will start one after another.",
        "La cola está vacía. Durante una descarga, rellena enlace, nombre y carpeta y pulsa «Añadir a la cola»: "
        "los vídeos se descargarán uno tras otro.",
        "La file d'attente est vide. Pendant un téléchargement, remplissez le lien, le nom et le dossier puis "
        "cliquez sur « Ajouter à la file » : les vidéos seront téléchargées l'une après l'autre.",
        "キューは空です。ダウンロード中にリンク・名前・保存先を入力して「キューに追加」を押すと、"
        "動画が順番にダウンロードされます。"),
    "queue_resumes": ("riprende da dove era rimasto", "resumes where it stopped", "continúa donde se quedó",
                      "reprend là où il s'était arrêté", "中断した所から再開"),
    "btn_start_queue": ("▶  Avvia coda", "▶  Start queue", "▶  Iniciar cola", "▶  Lancer la file", "▶  キューを開始"),
    "btn_clear_queue": ("Svuota coda", "Clear queue", "Vaciar cola", "Vider la file", "キューを空にする"),
    "job_label": ("{name}  ·  ancora {left} in coda", "{name}  ·  {left} more in queue",
                  "{name}  ·  {left} más en cola", "{name}  ·  encore {left} dans la file",
                  "{name}  ·  キューに残り {left} 件"),
    "job_label_single": ("{name}", "{name}", "{name}", "{name}", "{name}"),
    "job_label_paused": ("Coda in pausa: {n} da scaricare (premi «Avvia coda»)",
                         "Queue paused: {n} to download (press \"Start queue\")",
                         "Cola en pausa: {n} por descargar (pulsa «Iniciar cola»)",
                         "File en pause : {n} à télécharger (cliquez sur « Lancer la file »)",
                         "キュー一時停止中：残り {n} 件（「キューを開始」を押してください）"),
    "log_queue_added": ("[+] Aggiunto alla coda: {name} (in coda: {n})", "[+] Added to queue: {name} (queued: {n})",
                        "[+] Añadido a la cola: {name} (en cola: {n})", "[+] Ajouté à la file : {name} (en attente : {n})",
                        "[+] キューに追加：{name}（待機中：{n} 件）"),
    "log_queue_removed": ("[*] Tolto dalla coda: {name}", "[*] Removed from queue: {name}",
                          "[*] Quitado de la cola: {name}", "[*] Retiré de la file : {name}",
                          "[*] キューから削除：{name}"),
    "log_queue_cleared": ("[*] Coda svuotata.", "[*] Queue cleared.", "[*] Cola vaciada.", "[*] File vidée.",
                          "[*] キューを空にしました。"),
    "log_job_start": ("[*] Inizio download: {name}  →  {folder}", "[*] Starting download: {name}  →  {folder}",
                      "[*] Inicio de la descarga: {name}  →  {folder}",
                      "[*] Début du téléchargement : {name}  →  {folder}",
                      "[*] ダウンロード開始：{name}  →  {folder}"),
    "log_next_in_queue": ("[*] Passo al prossimo video della coda (ne restano {n}).",
                          "[*] Moving on to the next video in the queue ({n} left).",
                          "[*] Paso al siguiente vídeo de la cola (quedan {n}).",
                          "[*] Passage à la vidéo suivante de la file ({n} restantes).",
                          "[*] キューの次の動画に進みます（残り {n} 件）。"),
    "dlg_clear_queue_title": ("Svuota coda", "Clear queue", "Vaciar cola", "Vider la file", "キューを空にする"),
    "dlg_clear_queue_body": ("Vuoi togliere dalla coda tutti i {n} video in attesa?",
                             "Remove all {n} waiting videos from the queue?",
                             "¿Quitar de la cola los {n} vídeos en espera?",
                             "Retirer de la file les {n} vidéos en attente ?",
                             "待機中の {n} 件の動画をすべてキューから削除しますか？"),
    "dlg_duplicate_title": ("Già in coda", "Already queued", "Ya en cola", "Déjà dans la file", "既にキューにあります"),
    "dlg_duplicate_body": (
        "«{name}» in questa cartella è già in download o in coda.\nScegli un altro nome o un'altra cartella.",
        "\"{name}\" in this folder is already downloading or queued.\nChoose another name or folder.",
        "«{name}» en esta carpeta ya se está descargando o está en cola.\nElige otro nombre u otra carpeta.",
        "« {name} » dans ce dossier est déjà en téléchargement ou dans la file.\nChoisissez un autre nom ou dossier.",
        "このフォルダーの「{name}」は既にダウンロード中かキューにあります。\n別の名前か保存先を選んでください。"),
    "dlg_batch_title": ("Coda completata", "Queue finished", "Cola terminada", "File terminée", "キュー完了"),
    "dlg_batch_body": ("Video scaricati: {done}\nNon riusciti: {failed}", "Videos downloaded: {done}\nFailed: {failed}",
                       "Vídeos descargados: {done}\nFallidos: {failed}", "Vidéos téléchargées : {done}\nÉchecs : {failed}",
                       "ダウンロード完了：{done} 件\n失敗：{failed} 件"),
    "batch_incomplete": ("incompleto ({progress})", "incomplete ({progress})", "incompleto ({progress})",
                         "incomplet ({progress})", "未完了（{progress}）"),
    "dlg_batch_failed_hint": (
        "Le parti già scaricate sono conservate: rimetti in coda lo stesso link con lo stesso nome per riprendere. "
        "I dettagli sono nel Registro.",
        "Parts already downloaded are kept: queue the same link with the same name again to resume. "
        "Details are in the Log.",
        "Las partes ya descargadas se conservan: vuelve a poner en cola el mismo enlace con el mismo nombre para "
        "continuar. Los detalles están en el Registro.",
        "Les parties déjà téléchargées sont conservées : remettez le même lien avec le même nom dans la file pour "
        "reprendre. Les détails sont dans le Journal.",
        "ダウンロード済みの部分は保存されています。同じリンクを同じ名前でキューに入れ直すと再開できます。"
        "詳細はログをご覧ください。"),
    "dlg_open_folder_question": ("Vuoi aprire la cartella?", "Open the folder?", "¿Abrir la carpeta?",
                                 "Ouvrir le dossier ?", "フォルダーを開きますか？"),

    # --- Stato ---
    "status_ready": ("Pronto", "Ready", "Listo", "Prêt", "準備完了"),
    "status_ready_sub": ("Inserisci il link e premi Scarica", "Enter the link and press Download",
                         "Introduce el enlace y pulsa Descargar", "Saisissez le lien et cliquez sur Télécharger",
                         "リンクを入力して「ダウンロード」を押してください"),
    "status_vpn_check": ("Controllo della VPN…", "Checking the VPN…", "Comprobando la VPN…", "Vérification du VPN…",
                         "VPNを確認中…"),
    "status_vpn_check_sub": ("Verifico la connessione prima di aprire il sito",
                             "Checking the connection before opening the site",
                             "Compruebo la conexión antes de abrir el sitio",
                             "Vérification de la connexion avant d'ouvrir le site",
                             "サイトを開く前に接続を確認しています"),
    "status_searching": ("Ricerca del flusso video…", "Looking for the video stream…", "Buscando el flujo de vídeo…",
                         "Recherche du flux vidéo…", "動画ストリームを検索中…"),
    "status_searching_sub": ("{browser} si apre da solo: se vedi pop-up, clicca sul player",
                             "{browser} opens by itself: if you see pop-ups, click the player",
                             "{browser} se abre solo: si ves ventanas emergentes, haz clic en el reproductor",
                             "{browser} s'ouvre tout seul : si des pop-ups apparaissent, cliquez sur le lecteur",
                             "{browser} が自動で開きます。ポップアップが出たらプレーヤーをクリックしてください"),
    "status_reconnecting": ("Riconnessione al sito…", "Reconnecting to the site…", "Reconectando con el sitio…",
                            "Reconnexion au site…", "サイトに再接続中…"),
    "status_reconnecting_sub": ("{browser} si riapre per ottenere un nuovo collegamento",
                                "{browser} reopens to get a new link", "{browser} se vuelve a abrir para obtener un enlace nuevo",
                                "{browser} se rouvre pour obtenir un nouveau lien",
                                "新しいリンクを取得するため {browser} を再度開きます"),
    "status_downloading": ("Download in corso", "Downloading", "Descargando", "Téléchargement en cours",
                           "ダウンロード中"),
    "status_connecting_sub": ("Connessione al server…", "Connecting to the server…", "Conectando con el servidor…",
                              "Connexion au serveur…", "サーバーに接続中…"),
    "status_resumed_sub": ("Ripresa {progress}", "Resumed {progress}", "Reanudada {progress}", "Reprise {progress}",
                           "{progress}から再開"),
    "status_finish_at": ("Fine prevista verso le {time}", "Expected to finish around {time}",
                         "Fin prevista hacia las {time}", "Fin prévue vers {time}", "{time} 頃に完了予定"),
    "status_calculating_sub": ("Calcolo del tempo rimanente…", "Calculating time left…",
                               "Calculando el tiempo restante…", "Calcul du temps restant…", "残り時間を計算中…"),
    "status_merging": ("Creazione del file MP4…", "Creating the MP4 file…", "Creando el archivo MP4…",
                       "Création du fichier MP4…", "MP4ファイルを作成中…"),
    "status_merging_sub": ("Unione di video e audio, senza ricodifica", "Joining video and audio, without re-encoding",
                           "Uniendo vídeo y audio, sin recodificar", "Assemblage de la vidéo et de l'audio, sans réencodage",
                           "映像と音声を結合中（再エンコードなし）"),
    "status_merging_percent": ("Unione di video e audio: {percent}", "Joining video and audio: {percent}",
                               "Uniendo vídeo y audio: {percent}", "Assemblage vidéo et audio : {percent}",
                               "映像と音声を結合中：{percent}"),
    "status_merging_final": ("Scrittura della parte finale del file", "Writing the end of the file",
                             "Escribiendo la parte final del archivo", "Écriture de la fin du fichier",
                             "ファイルの最後の部分を書き込み中"),
    "status_cleanup": ("Quasi finito…", "Almost done…", "Casi listo…", "Presque fini…", "まもなく完了…"),
    "status_cleanup_sub": ("Eliminazione dei file temporanei", "Deleting temporary files",
                           "Eliminando los archivos temporales", "Suppression des fichiers temporaires",
                           "一時ファイルを削除中"),
    "status_done": ("Download completato", "Download complete", "Descarga completada", "Téléchargement terminé",
                    "ダウンロード完了"),
    "status_cancelling": ("Annullamento in corso…", "Cancelling…", "Cancelando…", "Annulation…", "キャンセル中…"),
    "status_cancelling_sub": ("Chiusura del browser e dei download in corso", "Closing the browser and the downloads",
                              "Cerrando el navegador y las descargas", "Fermeture du navigateur et des téléchargements",
                              "ブラウザーとダウンロードを終了しています"),
    "status_paused": ("Download in pausa", "Download paused", "Descarga en pausa", "Téléchargement en pause",
                      "ダウンロード一時停止"),
    "status_paused_sub": ("Arrivato {progress}: è tornato in cima alla coda, premi «Avvia coda» per riprendere",
                          "Reached {progress}: it is back at the top of the queue, press \"Start queue\" to resume",
                          "Llegó {progress}: ha vuelto al principio de la cola, pulsa «Iniciar cola» para continuar",
                          "Arrivé {progress} : il est revenu en tête de la file, cliquez sur « Lancer la file » "
                          "pour reprendre",
                          "{progress}まで完了：キューの先頭に戻しました。「キューを開始」で再開します"),
    "status_cancelled": ("Download annullato", "Download cancelled", "Descarga cancelada", "Téléchargement annulé",
                         "ダウンロードをキャンセルしました"),
    "status_cancelled_sub": ("Nessun dato scaricato: il video è tornato in coda (toglilo con ✕ se non ti serve)",
                             "Nothing downloaded: the video is back in the queue (remove it with ✕ if you don't "
                             "need it)",
                             "No se descargó nada: el vídeo ha vuelto a la cola (quítalo con ✕ si no lo necesitas)",
                             "Rien n'a été téléchargé : la vidéo est revenue dans la file (retirez-la avec ✕ si "
                             "besoin)",
                             "何もダウンロードされていません：動画はキューに戻りました（不要なら ✕ で削除）"),
    "status_incomplete": ("Download incompleto", "Download incomplete", "Descarga incompleta",
                          "Téléchargement incomplet", "ダウンロード未完了"),
    "status_incomplete_sub": ("Arrivato {progress}: la parte scaricata è conservata",
                              "Reached {progress}: the downloaded part is kept",
                              "Llegó {progress}: la parte descargada se conserva",
                              "Arrivé {progress} : la partie téléchargée est conservée",
                              "{progress}まで完了：ダウンロード済みの部分は保存されています"),
    "status_error": ("Errore", "Error", "Error", "Erreur", "エラー"),
    "status_not_started": ("Download non avviato", "Download not started", "Descarga no iniciada",
                           "Téléchargement non lancé", "ダウンロードは開始されませんでした"),
    "status_not_started_sub": ("Attiva la VPN e premi «Avvia coda»", "Turn on the VPN and press \"Start queue\"",
                               "Activa la VPN y pulsa «Iniciar cola»", "Activez le VPN et cliquez sur « Lancer la file »",
                               "VPNを有効にして「キューを開始」を押してください"),
    "title_percent": ("{percent} · {app}", "{percent} · {app}", "{percent} · {app}", "{percent} · {app}",
                      "{percent} · {app}"),
    "title_merge": ("Unione {percent} · {app}", "Joining {percent} · {app}", "Uniendo {percent} · {app}",
                    "Assemblage {percent} · {app}", "結合 {percent} · {app}"),
    "title_done": ("✔ Completato · {app}", "✔ Completed · {app}", "✔ Completado · {app}", "✔ Terminé · {app}",
                   "✔ 完了 · {app}"),

    # --- Controlli ---
    "vpn_checking": ("Verifica…", "Checking…", "Comprobando…", "Vérification…", "確認中…"),
    "vpn_checking_detail": ("Controllo della connessione in corso", "Checking the connection",
                            "Comprobando la conexión", "Vérification de la connexion", "接続を確認しています"),
    "vpn_active": ("VPN attiva", "VPN active", "VPN activa", "VPN actif", "VPN有効"),
    "vpn_inactive": ("Nessuna VPN rilevata", "No VPN detected", "No se detecta VPN", "Aucun VPN détecté",
                     "VPNが検出されません"),
    "vpn_ip": ("IP {ip} · {country} · {isp}", "IP {ip} · {country} · {isp}", "IP {ip} · {country} · {isp}",
               "IP {ip} · {country} · {isp}", "IP {ip} · {country} · {isp}"),
    "vpn_ip_unverifiable": ("IP pubblico non verificabile ({err})", "Public IP could not be checked ({err})",
                            "No se puede comprobar la IP pública ({err})", "IP publique non vérifiable ({err})",
                            "グローバルIPを確認できません（{err}）"),
    "vpn_ip_blocked": ("IP pubblico non verificabile: i servizi di controllo non sono raggiungibili (forse bloccati "
                       "dal blocco pubblicità/tracker della VPN, es. NetShield)",
                       "Public IP could not be checked: the check services are unreachable (possibly blocked by "
                       "the VPN's ad/tracker blocker, e.g. NetShield)",
                       "No se puede comprobar la IP pública: los servicios de comprobación no responden (quizá "
                       "bloqueados por el bloqueador de anuncios/rastreadores de la VPN, p. ej. NetShield)",
                       "IP publique non vérifiable : les services de vérification sont injoignables (peut-être "
                       "bloqués par le bloqueur de pubs/traqueurs du VPN, ex. NetShield)",
                       "グローバルIPを確認できません：確認サービスに接続できません（VPN の広告・トラッカーブロック"
                       "（例：NetShield）によるブロックの可能性）"),
    "vpn_adapter": (" · scheda: {name}", " · adapter: {name}", " · adaptador: {name}", " · carte : {name}",
                    " · アダプター：{name}"),
    "ip_invalid_response": ("risposta non valida", "invalid response", "respuesta no válida", "réponse non valide",
                            "無効な応答"),
    "log_vpn": ("[*] Controllo VPN: {state} — {details}", "[*] VPN check: {state} — {details}",
                "[*] Comprobación de VPN: {state} — {details}", "[*] Vérification VPN : {state} — {details}",
                "[*] VPN確認：{state} — {details}"),
    "browser_none": ("Nessun browser compatibile", "No compatible browser", "Ningún navegador compatible",
                     "Aucun navigateur compatible", "対応ブラウザーがありません"),
    "browser_none_detail": ("Serve Brave, Chrome, Edge o Vivaldi: installane uno o indicalo con «Cambia…»",
                            "Brave, Chrome, Edge or Vivaldi is needed: install one or select it with \"Change…\"",
                            "Se necesita Brave, Chrome, Edge o Vivaldi: instala uno o indícalo con «Cambiar…»",
                            "Brave, Chrome, Edge ou Vivaldi est nécessaire : installez-en un ou indiquez-le avec "
                            "« Changer… »",
                            "Brave・Chrome・Edge・Vivaldi のいずれかが必要です。インストールするか「変更…」で指定してください"),
    "note_default": ("Browser predefinito", "Default browser", "Navegador predeterminado", "Navigateur par défaut",
                     "既定のブラウザー"),
    "note_incompatible": ("Il predefinito ({name}) non è compatibile, uso questo",
                          "The default ({name}) is not compatible, using this one",
                          "El predeterminado ({name}) no es compatible, uso este",
                          "Le navigateur par défaut ({name}) n'est pas compatible, utilisation de celui-ci",
                          "既定のブラウザー（{name}）は非対応のため、こちらを使用します"),
    "note_not_detected": ("Browser predefinito non rilevato, uso questo", "Default browser not detected, using this one",
                          "No se detecta el navegador predeterminado, uso este",
                          "Navigateur par défaut non détecté, utilisation de celui-ci",
                          "既定のブラウザーを検出できないため、こちらを使用します"),
    "note_manual": ("Scelto a mano", "Chosen manually", "Elegido manualmente", "Choisi manuellement", "手動で選択"),
    "ffmpeg_found": ("Trovato", "Found", "Encontrado", "Trouvé", "検出済み"),
    "ffmpeg_missing": ("Non trovato", "Not found", "No encontrado", "Introuvable", "見つかりません"),
    "ffmpeg_missing_detail": ("Mettilo nella cartella del programma oppure: winget install Gyan.FFmpeg",
                              "Put it in the program folder or run: winget install Gyan.FFmpeg",
                              "Ponlo en la carpeta del programa o ejecuta: winget install Gyan.FFmpeg",
                              "Placez-le dans le dossier du programme ou lancez : winget install Gyan.FFmpeg",
                              "プログラムのフォルダーに置くか、次を実行してください：winget install Gyan.FFmpeg"),

    # --- Finestre di dialogo ---
    "dlg_error_title": ("Errore", "Error", "Error", "Erreur", "エラー"),
    "dlg_missing_libs_title": ("Librerie mancanti", "Missing libraries", "Faltan bibliotecas", "Bibliothèques manquantes",
                               "ライブラリが不足しています"),
    "dlg_missing_libs_body": ("Mancano queste librerie: {libs}.\n\nApri il terminale ed esegui:\n    python -m pip install {cmd}",
                              "These libraries are missing: {libs}.\n\nOpen a terminal and run:\n    python -m pip install {cmd}",
                              "Faltan estas bibliotecas: {libs}.\n\nAbre el terminal y ejecuta:\n    python -m pip install {cmd}",
                              "Ces bibliothèques manquent : {libs}.\n\nOuvrez un terminal et lancez :\n    python -m pip install {cmd}",
                              "次のライブラリがありません：{libs}\n\nターミナルで次を実行してください：\n    python -m pip install {cmd}"),
    "dlg_invalid_url_title": ("URL non valido", "Invalid URL", "URL no válida", "URL non valide", "無効なURL"),
    "dlg_invalid_url_body": ("Inserisci l'indirizzo completo della pagina del video (deve iniziare con http:// o https://).",
                             "Enter the full address of the video page (it must start with http:// or https://).",
                             "Introduce la dirección completa de la página del vídeo (debe empezar por http:// o https://).",
                             "Saisissez l'adresse complète de la page de la vidéo (elle doit commencer par http:// ou https://).",
                             "動画ページの完全なアドレスを入力してください（http:// または https:// で始まる必要があります）。"),
    "dlg_invalid_name_title": ("Nome non valido", "Invalid name", "Nombre no válido", "Nom non valide", "無効な名前"),
    "dlg_invalid_name_body": ("Inserisci il nome con cui salvare il video.", "Enter the name to save the video as.",
                              "Introduce el nombre con el que guardar el vídeo.",
                              "Saisissez le nom sous lequel enregistrer la vidéo.",
                              "動画を保存する名前を入力してください。"),
    "dlg_missing_folder_title": ("Cartella mancante", "Missing folder", "Falta la carpeta", "Dossier manquant",
                                 "保存先がありません"),
    "dlg_missing_folder_body": ("Scegli la cartella in cui salvare il video.", "Choose the folder to save the video in.",
                                "Elige la carpeta donde guardar el vídeo.",
                                "Choisissez le dossier où enregistrer la vidéo.",
                                "動画の保存先フォルダーを選んでください。"),
    "dlg_folder_missing_title": ("Cartella inesistente", "Folder does not exist", "La carpeta no existe",
                                 "Dossier inexistant", "フォルダーが存在しません"),
    "dlg_folder_missing_body": ("La cartella\n{folder}\nnon esiste. Vuoi crearla?",
                                "The folder\n{folder}\ndoes not exist. Create it?",
                                "La carpeta\n{folder}\nno existe. ¿Quieres crearla?",
                                "Le dossier\n{folder}\nn'existe pas. Voulez-vous le créer ?",
                                "フォルダー\n{folder}\nは存在しません。作成しますか？"),
    "dlg_create_folder_error": ("Impossibile creare la cartella:\n{err}", "Could not create the folder:\n{err}",
                                "No se puede crear la carpeta:\n{err}", "Impossible de créer le dossier :\n{err}",
                                "フォルダーを作成できません：\n{err}"),
    "dlg_open_folder_error": ("Impossibile aprire la cartella:\n{err}", "Could not open the folder:\n{err}",
                              "No se puede abrir la carpeta:\n{err}", "Impossible d'ouvrir le dossier :\n{err}",
                              "フォルダーを開けません：\n{err}"),
    "dlg_choose_folder": ("Scegli dove salvare il video", "Choose where to save the video",
                          "Elige dónde guardar el vídeo", "Choisissez où enregistrer la vidéo",
                          "動画の保存先を選択"),
    "dlg_choose_browser": ("Seleziona l'eseguibile del browser", "Select the browser executable",
                           "Selecciona el ejecutable del navegador", "Sélectionnez l'exécutable du navigateur",
                           "ブラウザーの実行ファイルを選択"),
    "filetype_browser": ("Browser", "Browser", "Navegador", "Navigateur", "ブラウザー"),
    "filetype_all": ("Tutti i file", "All files", "Todos los archivos", "Tous les fichiers", "すべてのファイル"),
    "dlg_browser_unknown_title": ("Browser non riconosciuto", "Browser not recognised", "Navegador no reconocido",
                                  "Navigateur non reconnu", "認識できないブラウザー"),
    "dlg_browser_unknown_body": (
        "{name} non risulta tra i browser compatibili (Brave, Chrome, Edge, Vivaldi): funzionano solo quelli basati "
        "su Chromium.\n\nVuoi provarlo comunque?",
        "{name} is not among the compatible browsers (Brave, Chrome, Edge, Vivaldi): only Chromium-based browsers "
        "work.\n\nTry it anyway?",
        "{name} no está entre los navegadores compatibles (Brave, Chrome, Edge, Vivaldi): solo funcionan los basados "
        "en Chromium.\n\n¿Probarlo de todos modos?",
        "{name} ne fait pas partie des navigateurs compatibles (Brave, Chrome, Edge, Vivaldi) : seuls ceux basés sur "
        "Chromium fonctionnent.\n\nL'essayer quand même ?",
        "{name} は対応ブラウザー（Brave・Chrome・Edge・Vivaldi）ではありません。Chromium ベースのブラウザーのみ動作します。"
        "\n\nそれでも試しますか？"),
    "dlg_browser_missing_title": ("Browser non trovato", "Browser not found", "Navegador no encontrado",
                                  "Navigateur introuvable", "ブラウザーが見つかりません"),
    "dlg_browser_missing_body": (
        "Serve un browser basato su Chromium (Brave, Chrome, Edge o Vivaldi): installane uno oppure indicalo con il "
        "pulsante «Cambia…».",
        "A Chromium-based browser is needed (Brave, Chrome, Edge or Vivaldi): install one or select it with the "
        "\"Change…\" button.",
        "Se necesita un navegador basado en Chromium (Brave, Chrome, Edge o Vivaldi): instala uno o indícalo con el "
        "botón «Cambiar…».",
        "Un navigateur basé sur Chromium est nécessaire (Brave, Chrome, Edge ou Vivaldi) : installez-en un ou "
        "indiquez-le avec le bouton « Changer… ».",
        "Chromium ベースのブラウザー（Brave・Chrome・Edge・Vivaldi）が必要です。インストールするか「変更…」ボタンで指定してください。"),
    "dlg_ffmpeg_missing_title": ("FFmpeg non trovato", "FFmpeg not found", "FFmpeg no encontrado", "FFmpeg introuvable",
                                 "FFmpeg が見つかりません"),
    "dlg_ffmpeg_missing_body": (
        "Metti ffmpeg.exe nella cartella del programma oppure installalo (winget install Gyan.FFmpeg) e riavvia.",
        "Put ffmpeg.exe in the program folder or install it (winget install Gyan.FFmpeg) and restart.",
        "Pon ffmpeg.exe en la carpeta del programa o instálalo (winget install Gyan.FFmpeg) y reinicia.",
        "Placez ffmpeg.exe dans le dossier du programme ou installez-le (winget install Gyan.FFmpeg) puis redémarrez.",
        "ffmpeg.exe をプログラムのフォルダーに置くか、インストール（winget install Gyan.FFmpeg）して再起動してください。"),
    "dlg_interrupted_title": ("Download interrotto", "Interrupted download", "Descarga interrumpida",
                              "Téléchargement interrompu", "中断されたダウンロード"),
    "dlg_resume_body": (
        "C'è un download interrotto di «{name}», arrivato {progress}.\n\nVuoi riprenderlo da lì?\n\n"
        "Sì = riprendi    No = ricomincia da capo",
        "There is an interrupted download of \"{name}\", stopped {progress}.\n\nResume it from there?\n\n"
        "Yes = resume    No = start over",
        "Hay una descarga interrumpida de «{name}», que llegó {progress}.\n\n¿Quieres continuarla desde ahí?\n\n"
        "Sí = continuar    No = empezar de nuevo",
        "Un téléchargement de « {name} » a été interrompu, arrivé {progress}.\n\nLe reprendre à partir de là ?\n\n"
        "Oui = reprendre    Non = recommencer",
        "「{name}」のダウンロードが{progress}で中断されています。\n\nそこから再開しますか？\n\n"
        "はい = 再開    いいえ = 最初からやり直す"),
    "dlg_other_page_body": (
        "C'è un download interrotto di un'altra pagina salvato come «{name}».\n\nVuoi eliminarlo e scaricare questo video?",
        "There is an interrupted download of another page saved as \"{name}\".\n\nDelete it and download this video?",
        "Hay una descarga interrumpida de otra página guardada como «{name}».\n\n¿Eliminarla y descargar este vídeo?",
        "Un téléchargement interrompu d'une autre page est enregistré sous « {name} ».\n\nLe supprimer et télécharger "
        "cette vidéo ?",
        "別のページの中断されたダウンロードが「{name}」として保存されています。\n\n削除してこの動画をダウンロードしますか？"),
    "dlg_orphan_body": (
        "Nella cartella c'è un download interrotto salvato come «{name}», ma senza le informazioni necessarie per "
        "riprenderlo.\n\nVuoi eliminarlo e ricominciare da capo?",
        "The folder contains an interrupted download saved as \"{name}\", but without the information needed to "
        "resume it.\n\nDelete it and start over?",
        "En la carpeta hay una descarga interrumpida guardada como «{name}», pero sin la información necesaria para "
        "continuarla.\n\n¿Eliminarla y empezar de nuevo?",
        "Le dossier contient un téléchargement interrompu enregistré sous « {name} », mais sans les informations "
        "nécessaires pour le reprendre.\n\nLe supprimer et recommencer ?",
        "フォルダーに「{name}」として中断されたダウンロードがありますが、再開に必要な情報がありません。"
        "\n\n削除して最初からやり直しますか？"),
    "dlg_exists_title": ("File esistente", "File exists", "El archivo existe", "Fichier existant",
                         "ファイルが既にあります"),
    "dlg_exists_body": ("«{name}» esiste già in questa cartella.\nVuoi sovrascriverlo?",
                        "\"{name}\" already exists in this folder.\nOverwrite it?",
                        "«{name}» ya existe en esta carpeta.\n¿Sobrescribirlo?",
                        "« {name} » existe déjà dans ce dossier.\nL'écraser ?",
                        "「{name}」はこのフォルダーに既にあります。\n上書きしますか？"),
    "dlg_close_title": ("Download in corso", "Download in progress", "Descarga en curso", "Téléchargement en cours",
                        "ダウンロード中"),
    "dlg_close_body": (
        "C'è un download in corso o in coda (in coda: {n}).\nVuoi interrompere e chiudere?\n\n"
        "Le parti già scaricate restano salvate; la coda non viene conservata.",
        "A download is running or queued (queued: {n}).\nStop and close?\n\n"
        "Parts already downloaded stay saved; the queue is not kept.",
        "Hay una descarga en curso o en cola (en cola: {n}).\n¿Interrumpir y cerrar?\n\n"
        "Las partes ya descargadas se conservan; la cola no se guarda.",
        "Un téléchargement est en cours ou en attente (en attente : {n}).\nInterrompre et fermer ?\n\n"
        "Les parties déjà téléchargées restent enregistrées ; la file n'est pas conservée.",
        "ダウンロード中、またはキューに待機中の動画があります（待機中：{n} 件）。\n中断して閉じますか？\n\n"
        "ダウンロード済みの部分は保存されますが、キューは保持されません。"),
    "dlg_no_vpn_title": ("VPN non rilevata", "VPN not detected", "VPN no detectada", "VPN non détecté",
                         "VPNが検出されません"),
    "dlg_no_vpn_body": ("Non risulta attiva nessuna VPN: il sito vedrà il tuo indirizzo IP reale.\n\n{details}\n\n"
                        "Vuoi continuare comunque?",
                        "No VPN appears to be active: the site will see your real IP address.\n\n{details}\n\n"
                        "Continue anyway?",
                        "No parece haber ninguna VPN activa: el sitio verá tu dirección IP real.\n\n{details}\n\n"
                        "¿Continuar de todos modos?",
                        "Aucun VPN ne semble actif : le site verra votre adresse IP réelle.\n\n{details}\n\n"
                        "Continuer quand même ?",
                        "有効なVPNが見つかりません。サイトにはあなたの実際のIPアドレスが見えます。\n\n{details}\n\n"
                        "それでも続けますか？"),
    "dlg_done_title": ("Download completato", "Download complete", "Descarga completada", "Téléchargement terminé",
                       "ダウンロード完了"),
    "dlg_done_body": ("Video salvato in:\n{path}\n\nVuoi aprire la cartella?", "Video saved to:\n{path}\n\nOpen the folder?",
                      "Vídeo guardado en:\n{path}\n\n¿Abrir la carpeta?",
                      "Vidéo enregistrée dans :\n{path}\n\nOuvrir le dossier ?",
                      "動画の保存先：\n{path}\n\nフォルダーを開きますか？"),
    "dlg_incomplete_title": ("Download incompleto", "Download incomplete", "Descarga incompleta",
                             "Téléchargement incomplet", "ダウンロード未完了"),
    "dlg_incomplete_body": (
        "Il server ha smesso di inviare il video (arrivato {progress}) e continua a rifiutarlo anche riaprendo la "
        "pagina.\n\nLa parte già scaricata è conservata. Prova a cambiare server della VPN oppure aspetta qualche "
        "minuto, poi premi di nuovo Scarica con lo stesso link e lo stesso nome: il download riprenderà da dove si è "
        "fermato.",
        "The server stopped sending the video (reached {progress}) and keeps refusing it even after reopening the "
        "page.\n\nThe part already downloaded is kept. Try another VPN server or wait a few minutes, then press "
        "Download again with the same link and name: the download will resume where it stopped.",
        "El servidor dejó de enviar el vídeo (llegó {progress}) y lo sigue rechazando aunque se vuelva a abrir la "
        "página.\n\nLa parte ya descargada se conserva. Prueba otro servidor de la VPN o espera unos minutos y pulsa "
        "Descargar de nuevo con el mismo enlace y nombre: la descarga continuará donde se quedó.",
        "Le serveur a cessé d'envoyer la vidéo (arrivé {progress}) et continue de la refuser même après réouverture "
        "de la page.\n\nLa partie déjà téléchargée est conservée. Essayez un autre serveur VPN ou attendez quelques "
        "minutes, puis cliquez à nouveau sur Télécharger avec le même lien et le même nom : le téléchargement "
        "reprendra là où il s'est arrêté.",
        "サーバーが動画の送信を停止し（{progress}まで完了）、ページを開き直しても拒否され続けています。\n\n"
        "ダウンロード済みの部分は保存されています。VPNのサーバーを変えるか数分待ってから、同じリンクと名前で"
        "もう一度「ダウンロード」を押すと、中断した所から再開します。"),

    # --- Registro e messaggi del download ---
    "log_cancel_requested": ("[*] Annullamento richiesto...", "[*] Cancellation requested...",
                             "[*] Cancelación solicitada...", "[*] Annulation demandée...",
                             "[*] キャンセルを要求しました..."),
    "log_cancelled": ("[*] Operazione interrotta dall'utente.", "[*] Operation stopped by the user.",
                      "[*] Operación interrumpida por el usuario.", "[*] Opération interrompue par l'utilisateur.",
                      "[*] ユーザーが操作を中断しました。"),
    "log_incomplete": ("[!] Il server continua a rifiutare i segmenti: download fermo {progress}.",
                       "[!] The server keeps refusing the segments: download stopped {progress}.",
                       "[!] El servidor sigue rechazando los segmentos: descarga detenida {progress}.",
                       "[!] Le serveur continue de refuser les segments : téléchargement arrêté {progress}.",
                       "[!] サーバーがセグメントを拒否し続けています：{progress}で停止しました。"),
    "log_error": ("[ERRORE] {err}", "[ERROR] {err}", "[ERROR] {err}", "[ERREUR] {err}", "[エラー] {err}"),
    "log_vpn_still_missing": ("[!] Nessuna VPN rilevata: proseguo come confermato all'avvio della coda.",
                              "[!] No VPN detected: continuing as confirmed when the queue started.",
                              "[!] No se detecta VPN: continúo como se confirmó al iniciar la cola.",
                              "[!] Aucun VPN détecté : je continue comme confirmé au lancement de la file.",
                              "[!] VPNが検出されません。キュー開始時の確認どおり続行します。"),
    "log_not_started_vpn": ("[!] Download non avviato: nessuna VPN attiva.", "[!] Download not started: no active VPN.",
                            "[!] Descarga no iniciada: ninguna VPN activa.",
                            "[!] Téléchargement non lancé : aucun VPN actif.",
                            "[!] ダウンロードは開始されませんでした：VPNが有効ではありません。"),
    "log_all_segments_present": (
        "[*] Tutti i segmenti sono già stati scaricati: passo direttamente alla creazione del file MP4.",
        "[*] All segments are already downloaded: going straight to creating the MP4 file.",
        "[*] Todos los segmentos ya están descargados: paso directamente a crear el archivo MP4.",
        "[*] Tous les segments sont déjà téléchargés : passage direct à la création du fichier MP4.",
        "[*] すべてのセグメントがダウンロード済みです。MP4ファイルの作成に進みます。"),
    "log_resuming": ("[*] Ripresa del download {progress} con {workers} connessioni",
                     "[*] Resuming the download {progress} with {workers} connections",
                     "[*] Reanudando la descarga {progress} con {workers} conexiones",
                     "[*] Reprise du téléchargement {progress} avec {workers} connexions",
                     "[*] {workers} 本の接続で{progress}からダウンロードを再開"),
    "log_tracks": ("[*] Video {video} · audio: {audio} · {segments} segmenti · {workers} connessioni",
                   "[*] Video {video} · audio: {audio} · {segments} segments · {workers} connections",
                   "[*] Vídeo {video} · audio: {audio} · {segments} segmentos · {workers} conexiones",
                   "[*] Vidéo {video} · audio : {audio} · {segments} segments · {workers} connexions",
                   "[*] 映像 {video} · 音声：{audio} · {segments} セグメント · 接続 {workers} 本"),
    "audio_in_video": ("incluso nel video", "included in the video", "incluido en el vídeo", "inclus dans la vidéo",
                       "映像に含まれる"),
    "log_request_refused": ("[!] Il server ha rifiutato la richiesta ({err}): serve un nuovo collegamento.",
                            "[!] The server refused the request ({err}): a new link is needed.",
                            "[!] El servidor rechazó la petición ({err}): hace falta un enlace nuevo.",
                            "[!] Le serveur a refusé la requête ({err}) : un nouveau lien est nécessaire.",
                            "[!] サーバーがリクエストを拒否しました（{err}）。新しいリンクが必要です。"),
    "log_reopening": ("[*] Riapro la pagina per ottenere un nuovo collegamento (tentativo {attempt} di {total})...",
                      "[*] Reopening the page to get a new link (attempt {attempt} of {total})...",
                      "[*] Vuelvo a abrir la página para obtener un enlace nuevo (intento {attempt} de {total})...",
                      "[*] Réouverture de la page pour obtenir un nouveau lien (tentative {attempt} sur {total})...",
                      "[*] 新しいリンクを取得するためページを開き直します（{attempt}/{total} 回目）..."),
    "err_no_m3u8": (
        "Impossibile catturare l'URL M3U8.\n\nRiprova e, se la pagina mostra pop-up o pubblicità, clicca tu sul "
        "player nella finestra del browser entro {seconds} secondi.",
        "Could not capture the M3U8 URL.\n\nTry again and, if the page shows pop-ups or ads, click the player in "
        "the browser window yourself within {seconds} seconds.",
        "No se pudo capturar la URL M3U8.\n\nInténtalo de nuevo y, si la página muestra ventanas emergentes o "
        "anuncios, haz clic tú en el reproductor en la ventana del navegador en menos de {seconds} segundos.",
        "Impossible de capturer l'URL M3U8.\n\nRéessayez et, si la page affiche des pop-ups ou des publicités, "
        "cliquez vous-même sur le lecteur dans la fenêtre du navigateur dans les {seconds} secondes.",
        "M3U8 のURLを取得できませんでした。\n\nもう一度試してください。ページにポップアップや広告が表示される場合は、"
        "{seconds} 秒以内にブラウザーのウィンドウでプレーヤーをクリックしてください。"),
    "err_version_changed": (
        "Il sito ora fornisce il video in una versione diversa da quella già scaricata in parte:\n"
        "  prima: {before}\n  ora:   {now}\n\nRiprendere mescolerebbe le due versioni e il file risulterebbe "
        "rovinato. Riprova più tardi, oppure premi Scarica e scegli «No» per ricominciare da capo.",
        "The site now provides a different version of the video from the one partly downloaded:\n"
        "  before: {before}\n  now:    {now}\n\nResuming would mix the two versions and ruin the file. Try again "
        "later, or press Download and choose \"No\" to start over.",
        "El sitio ofrece ahora una versión del vídeo distinta de la ya descargada en parte:\n"
        "  antes: {before}\n  ahora: {now}\n\nContinuar mezclaría las dos versiones y el archivo quedaría dañado. "
        "Inténtalo más tarde o pulsa Descargar y elige «No» para empezar de nuevo.",
        "Le site fournit maintenant une version de la vidéo différente de celle déjà en partie téléchargée :\n"
        "  avant : {before}\n  maintenant : {now}\n\nReprendre mélangerait les deux versions et abîmerait le "
        "fichier. Réessayez plus tard, ou cliquez sur Télécharger et choisissez « Non » pour recommencer.",
        "サイトが提供する動画のバージョンが、途中までダウンロードしたものと異なります：\n"
        "  以前：{before}\n  現在：{now}\n\n再開すると2つのバージョンが混ざり、ファイルが壊れます。"
        "後でもう一度試すか、「ダウンロード」を押して「いいえ」を選び、最初からやり直してください。"),
    "err_refused_403": ("Il server rifiuta il download del video (accesso negato, errore 403).\n\n"
                        "Prova a cambiare server della VPN e riprova.",
                        "The server refuses to send the video (access denied, error 403).\n\n"
                        "Try another VPN server and try again.",
                        "El servidor rechaza la descarga del vídeo (acceso denegado, error 403).\n\n"
                        "Prueba otro servidor de la VPN e inténtalo de nuevo.",
                        "Le serveur refuse le téléchargement de la vidéo (accès refusé, erreur 403).\n\n"
                        "Essayez un autre serveur VPN et réessayez.",
                        "サーバーが動画のダウンロードを拒否しています（アクセス拒否、エラー403）。\n\n"
                        "VPNのサーバーを変えてもう一度試してください。"),
    "err_partial_kept": ("La parte già scaricata è conservata: premi di nuovo Scarica con lo stesso link e nome per "
                         "riprendere.",
                         "The part already downloaded is kept: press Download again with the same link and name to "
                         "resume.",
                         "La parte ya descargada se conserva: pulsa Descargar de nuevo con el mismo enlace y nombre "
                         "para continuar.",
                         "La partie déjà téléchargée est conservée : cliquez à nouveau sur Télécharger avec le même "
                         "lien et le même nom pour reprendre.",
                         "ダウンロード済みの部分は保存されています。同じリンクと名前でもう一度「ダウンロード」を押すと再開します。"),
    "progress_start": ("all'inizio", "at the start", "al principio", "au début", "最初"),
    "progress_percent": ("al {p}", "at {p}", "al {p}", "à {p}", "{p}"),
    "progress_time": ("a {t}", "at {t}", "en {t}", "à {t}", "{t}"),
    "dur_s": ("{s} s", "{s} s", "{s} s", "{s} s", "{s} 秒"),
    "dur_ms": ("{m} min {s:02d} s", "{m} min {s:02d} s", "{m} min {s:02d} s", "{m} min {s:02d} s",
               "{m} 分 {s:02d} 秒"),
    "dur_hm": ("{h} h {m:02d} min", "{h} h {m:02d} min", "{h} h {m:02d} min", "{h} h {m:02d} min",
               "{h} 時間 {m:02d} 分"),

    # --- Browser ---
    "log_launch_browser": ("[*] Avvio di {name}: {path}", "[*] Starting {name}: {path}", "[*] Iniciando {name}: {path}",
                           "[*] Lancement de {name} : {path}", "[*] {name} を起動：{path}"),
    "err_browser_launch": ("Impossibile avviare {name} ({path}):\n{err}", "Could not start {name} ({path}):\n{err}",
                           "No se puede iniciar {name} ({path}):\n{err}", "Impossible de lancer {name} ({path}) :\n{err}",
                           "{name} を起動できません（{path}）：\n{err}"),
    "log_stream_candidate": ("[+] Flusso trovato: playlist di {duration} · {url}",
                             "[+] Stream found: {duration} playlist · {url}",
                             "[+] Flujo encontrado: lista de {duration} · {url}",
                             "[+] Flux trouvé : playlist de {duration} · {url}",
                             "[+] ストリーム検出：{duration} のプレイリスト · {url}"),
    "log_stream_candidate_master": ("[+] Flusso trovato: playlist principale di {duration} · {url}",
                                    "[+] Stream found: main playlist of {duration} · {url}",
                                    "[+] Flujo encontrado: lista principal de {duration} · {url}",
                                    "[+] Flux trouvé : playlist principale de {duration} · {url}",
                                    "[+] ストリーム検出：{duration} のメインプレイリスト · {url}"),
    "log_stream_short": ("[*] Flusso breve, probabilmente una pubblicità: aspetto il video principale...",
                         "[*] Short stream, probably an ad: waiting for the main video...",
                         "[*] Flujo corto, probablemente un anuncio: esperando el vídeo principal...",
                         "[*] Flux court, probablement une publicité : attente de la vidéo principale...",
                         "[*] 短いストリーム（広告の可能性）：本編の動画を待っています..."),
    "log_stream_ignored": ("[!] Playlist ignorata ({err}): {url}", "[!] Playlist ignored ({err}): {url}",
                           "[!] Lista ignorada ({err}): {url}", "[!] Playlist ignorée ({err}) : {url}",
                           "[!] プレイリストを無視（{err}）：{url}"),
    "log_stream_chosen": ("[+] Video scelto ({duration}): {url}", "[+] Video chosen ({duration}): {url}",
                          "[+] Vídeo elegido ({duration}): {url}", "[+] Vidéo choisie ({duration}) : {url}",
                          "[+] 選択した動画（{duration}）：{url}"),
    "log_browser_headers": ("[*] Intestazioni inviate dal browser per la playlist: {names}",
                            "[*] Headers sent by the browser for the playlist: {names}",
                            "[*] Cabeceras enviadas por el navegador para la lista: {names}",
                            "[*] En-têtes envoyés par le navigateur pour la playlist : {names}",
                            "[*] プレイリストでブラウザが送ったヘッダー：{names}"),
    "log_browser_segment": ("[*] Pezzo scaricato dal browser: {info}", "[*] Segment fetched by the browser: {info}",
                            "[*] Segmento descargado por el navegador: {info}",
                            "[*] Segment téléchargé par le navigateur : {info}", "[*] ブラウザが取得したセグメント：{info}"),
    "log_refused_missing": ("[*] {n} pezzi rifiutati da recuperare: riapro la pagina solo per quelli.",
                            "[*] {n} refused segments to recover: reopening the page just for them.",
                            "[*] {n} segmentos rechazados por recuperar: reabro la página solo para ellos.",
                            "[*] {n} segments refusés à récupérer : je rouvre la page seulement pour eux.",
                            "[*] 拒否された {n} 個のセグメントを回収するため、ページを開き直します。"),
    "log_refusal_stats": ("[*] Prima del rifiuto: {ok} pezzi salvati, di cui {reused} riusati dal browser.",
                          "[*] Before the refusal: {ok} segments saved, {reused} of them reused from the browser.",
                          "[*] Antes del rechazo: {ok} segmentos guardados, {reused} reutilizados del navegador.",
                          "[*] Avant le refus : {ok} segments enregistrés, dont {reused} réutilisés du navigateur.",
                          "[*] 拒否の前に {ok} 個のセグメントを保存（うち {reused} 個はブラウザから再利用）。"),
    "log_browser_no_segments": ("[*] Il browser non ha scaricato pezzi del video prima della chiusura.",
                                "[*] The browser did not fetch any video segment before closing.",
                                "[*] El navegador no descargó segmentos del vídeo antes de cerrarse.",
                                "[*] Le navigateur n'a téléchargé aucun segment vidéo avant la fermeture.",
                                "[*] ブラウザは終了前に動画のセグメントを取得しませんでした。"),
    "log_cookies": ("[*] Cookie del browser riutilizzati per il download ({n}): evita il rifiuto (403) del server.",
                    "[*] Browser cookies reused for the download ({n}): avoids the server's 403 refusal.",
                    "[*] Cookies del navegador reutilizados para la descarga ({n}): evita el rechazo (403) del servidor.",
                    "[*] Cookies du navigateur réutilisés pour le téléchargement ({n}) : évite le refus (403) du serveur.",
                    "[*] ブラウザの Cookie をダウンロードに再利用（{n} 件）：サーバーの拒否（403）を回避します。"),
    "log_stream_too_short": ("[!] Il flusso più lungo trovato dura solo {duration}: potrebbe non essere il video "
                             "principale.",
                             "[!] The longest stream found lasts only {duration}: it may not be the main video.",
                             "[!] El flujo más largo encontrado dura solo {duration}: puede que no sea el vídeo "
                             "principal.",
                             "[!] Le flux le plus long trouvé ne dure que {duration} : ce n'est peut-être pas la "
                             "vidéo principale.",
                             "[!] 見つかった最長のストリームは {duration} しかありません：本編ではない可能性があります。"),
    "err_not_video_playlist": ("non è una playlist video", "not a video playlist", "no es una lista de vídeo",
                               "ce n'est pas une playlist vidéo", "動画のプレイリストではありません"),
    "log_incognito": ("[*] Browser aperto in incognito: cronologia, cookie e cache vengono eliminati alla chiusura.",
                      "[*] Browser opened in incognito mode: history, cookies and cache are deleted when it closes.",
                      "[*] Navegador abierto en modo incógnito: el historial, las cookies y la caché se borran al "
                      "cerrarlo.",
                      "[*] Navigateur ouvert en navigation privée : historique, cookies et cache sont supprimés à la "
                      "fermeture.",
                      "[*] シークレットモードでブラウザを開きました：履歴・Cookie・キャッシュは終了時に削除されます。"),
    "log_webrtc_disabled": ("[*] WebRTC disattivato nel browser: il sito non può leggere gli indirizzi di rete del PC.",
                            "[*] WebRTC disabled in the browser: the site cannot read the PC's network addresses.",
                            "[*] WebRTC desactivado en el navegador: el sitio no puede leer las direcciones de red "
                            "del PC.",
                            "[*] WebRTC désactivé dans le navigateur : le site ne peut pas lire les adresses réseau "
                            "du PC.",
                            "[*] ブラウザの WebRTC を無効化：サイトは PC のネットワークアドレスを読み取れません。"),
    "log_navigating": ("[*] Navigazione verso: {url}", "[*] Opening: {url}", "[*] Abriendo: {url}",
                       "[*] Ouverture de : {url}", "[*] 移動中：{url}"),
    "log_page_warning": ("[!] Avviso durante il caricamento pagina: {err}", "[!] Warning while loading the page: {err}",
                         "[!] Aviso al cargar la página: {err}", "[!] Avertissement au chargement de la page : {err}",
                         "[!] ページ読み込み中の警告：{err}"),
    "log_searching_player": ("[*] Ricerca del player e avvio della riproduzione...",
                             "[*] Looking for the player and starting playback...",
                             "[*] Buscando el reproductor e iniciando la reproducción...",
                             "[*] Recherche du lecteur et lancement de la lecture...",
                             "[*] プレーヤーを探して再生を開始しています..."),
    "log_popups_blocked": ("[*] Pop-up e pubblicità bloccati: l'app avvia il player da sola.",
                           "[*] Pop-ups and ads blocked: the app starts the player by itself.",
                           "[*] Pop-ups y anuncios bloqueados: la app inicia el reproductor sola.",
                           "[*] Pop-ups et publicités bloqués : l'app lance le lecteur toute seule.",
                           "[*] ポップアップと広告をブロック：アプリが自動でプレーヤーを起動します。"),
    "log_popup_closed": ("[*] Pop-up pubblicitario chiuso in automatico.", "[*] Ad pop-up closed automatically.",
                         "[*] Pop-up publicitario cerrado automáticamente.",
                         "[*] Pop-up publicitaire fermé automatiquement.", "[*] 広告ポップアップを自動で閉じました。"),
    "log_ad_blocked": ("[*] Dirottamento pubblicitario della pagina bloccato: {url}",
                       "[*] Ad page hijack blocked: {url}", "[*] Secuestro publicitario de la página bloqueado: {url}",
                       "[*] Détournement publicitaire de la page bloqué : {url}",
                       "[*] 広告によるページ乗っ取りをブロック：{url}"),
    "log_waiting_stream": ("[*] In attesa del flusso (max {seconds} s). Se il player non parte, premi tu Play "
                           "nella finestra del browser.",
                           "[*] Waiting for the stream (max {seconds} s). If the player does not start, press Play "
                           "in the browser window yourself.",
                           "[*] Esperando el flujo (máx. {seconds} s). Si el reproductor no arranca, pulsa tú Play "
                           "en la ventana del navegador.",
                           "[*] En attente du flux (max {seconds} s). Si le lecteur ne démarre pas, appuyez vous-même "
                           "sur Lecture dans la fenêtre du navigateur.",
                           "[*] ストリームを待っています（最大 {seconds} 秒）。プレーヤーが始まらない場合はブラウザーの"
                           "ウィンドウで再生を押してください。"),
    "log_timeout_stream": ("[!] Timeout: nessun flusso M3U8 intercettato automaticamente.",
                           "[!] Timeout: no M3U8 stream captured automatically.",
                           "[!] Tiempo agotado: no se capturó ningún flujo M3U8 automáticamente.",
                           "[!] Délai dépassé : aucun flux M3U8 capturé automatiquement.",
                           "[!] タイムアウト：M3U8 ストリームを自動取得できませんでした。"),

    # --- Rete e playlist ---
    "err_too_many_redirects": ("troppi reindirizzamenti", "too many redirects", "demasiadas redirecciones",
                               "trop de redirections", "リダイレクトが多すぎます"),
    "err_invalid_address": ("indirizzo non valido: {url}", "invalid address: {url}", "dirección no válida: {url}",
                            "adresse non valide : {url}", "無効なアドレス：{url}"),
    "err_aborted": ("download interrotto", "download stopped", "descarga interrumpida", "téléchargement interrompu",
                    "ダウンロードを中断しました"),
    "err_no_connection": ("connessione non disponibile", "connection unavailable", "conexión no disponible",
                          "connexion indisponible", "接続できません"),
    "err_aes_no_uri": ("La playlist indica una cifratura AES-128 ma non l'indirizzo della chiave.",
                       "The playlist declares AES-128 encryption but not the key address.",
                       "La lista indica un cifrado AES-128 pero no la dirección de la clave.",
                       "La playlist indique un chiffrement AES-128 mais pas l'adresse de la clé.",
                       "プレイリストに AES-128 暗号化の指定がありますが、鍵のアドレスがありません。"),
    "err_unsupported_protection": ("Il video usa una protezione non supportata ({method}).",
                                   "The video uses an unsupported protection ({method}).",
                                   "El vídeo usa una protección no compatible ({method}).",
                                   "La vidéo utilise une protection non prise en charge ({method}).",
                                   "この動画は対応していない保護方式（{method}）を使用しています。"),
    "err_no_segments": ("La playlist del video non contiene segmenti.", "The video playlist contains no segments.",
                        "La lista del vídeo no contiene segmentos.", "La playlist de la vidéo ne contient aucun segment.",
                        "動画のプレイリストにセグメントがありません。"),
    "err_no_variants": ("La playlist principale non contiene nessuna versione del video.",
                        "The main playlist contains no version of the video.",
                        "La lista principal no contiene ninguna versión del vídeo.",
                        "La playlist principale ne contient aucune version de la vidéo.",
                        "メインのプレイリストに動画のバージョンがありません。"),
    "tracks_desc": ("video {video} ({segments} segmenti)", "video {video} ({segments} segments)",
                    "vídeo {video} ({segments} segmentos)", "vidéo {video} ({segments} segments)",
                    "映像 {video}（{segments} セグメント）"),
    "tracks_desc_audio": (", audio {audio}", ", audio {audio}", ", audio {audio}", ", audio {audio}", "、音声 {audio}"),
    "what_init": ("inizio della traccia {track}", "start of track {track}", "inicio de la pista {track}",
                  "début de la piste {track}", "トラック {track} の先頭部分"),
    "what_segment": ("segmento {n} ({track})", "segment {n} ({track})", "segmento {n} ({track})",
                     "segment {n} ({track})", "セグメント {n}（{track}）"),
    "log_track_refused": ("[!] Il server ha rifiutato la traccia {track} ({err}): serve un nuovo collegamento.",
                          "[!] The server refused track {track} ({err}): a new link is needed.",
                          "[!] El servidor rechazó la pista {track} ({err}): hace falta un enlace nuevo.",
                          "[!] Le serveur a refusé la piste {track} ({err}) : un nouveau lien est nécessaire.",
                          "[!] サーバーがトラック {track} を拒否しました（{err}）。新しいリンクが必要です。"),
    "log_segment_refused": ("[!] Il server ha rifiutato il segmento {n} ({err}): serve un nuovo collegamento.",
                            "[!] The server refused segment {n} ({err}): a new link is needed.",
                            "[!] El servidor rechazó el segmento {n} ({err}): hace falta un enlace nuevo.",
                            "[!] Le serveur a refusé le segment {n} ({err}) : un nouveau lien est nécessaire.",
                            "[!] サーバーがセグメント {n} を拒否しました（{err}）。新しいリンクが必要です。"),
    "err_download_failed": ("Impossibile scaricare {what}: {err}", "Could not download {what}: {err}",
                            "No se puede descargar {what}: {err}", "Impossible de télécharger {what} : {err}",
                            "{what} をダウンロードできません：{err}"),
    "log_retry": ("[!] {what}: {err}. Nuovo tentativo tra {delay} s...", "[!] {what}: {err}. Retrying in {delay} s...",
                  "[!] {what}: {err}. Nuevo intento en {delay} s...", "[!] {what} : {err}. Nouvel essai dans {delay} s...",
                  "[!] {what}：{err}。{delay} 秒後に再試行します..."),
    "err_bad_key": ("chiave di decifratura non valida ({n} byte invece di 16)",
                    "invalid decryption key ({n} bytes instead of 16)",
                    "clave de descifrado no válida ({n} bytes en lugar de 16)",
                    "clé de déchiffrement non valide ({n} octets au lieu de 16)",
                    "無効な復号鍵（16 バイトではなく {n} バイト）"),
    "err_incomplete_encrypted": ("segmento cifrato incompleto", "incomplete encrypted segment",
                                 "segmento cifrado incompleto", "segment chiffré incomplet",
                                 "暗号化セグメントが不完全です"),

    # --- Sottotitoli ---
    "err_subs_encrypted": ("sottotitoli cifrati non supportati", "encrypted subtitles are not supported",
                           "subtítulos cifrados no compatibles", "sous-titres chiffrés non pris en charge",
                           "暗号化された字幕には対応していません"),
    "err_subs_empty": ("nessuna battuta trovata", "no lines found", "no se encontró ningún diálogo",
                       "aucune réplique trouvée", "字幕の行が見つかりません"),
    "log_subs_failed": ("[!] Sottotitoli «{name}» non scaricati: {err}", "[!] Subtitles \"{name}\" not downloaded: {err}",
                        "[!] Subtítulos «{name}» no descargados: {err}",
                        "[!] Sous-titres « {name} » non téléchargés : {err}",
                        "[!] 字幕「{name}」をダウンロードできません：{err}"),
    "log_subs_ok": ("[+] Sottotitoli «{name}» scaricati.", "[+] Subtitles \"{name}\" downloaded.",
                    "[+] Subtítulos «{name}» descargados.", "[+] Sous-titres « {name} » téléchargés.",
                    "[+] 字幕「{name}」をダウンロードしました。"),
    "log_subs_save_failed": ("[!] Impossibile salvare i sottotitoli {path}: {err}",
                             "[!] Could not save the subtitles {path}: {err}",
                             "[!] No se pueden guardar los subtítulos {path}: {err}",
                             "[!] Impossible d'enregistrer les sous-titres {path} : {err}",
                             "[!] 字幕 {path} を保存できません：{err}"),
    "log_subs_saved": ("[✓] Sottotitoli salvati: {files}", "[✓] Subtitles saved: {files}",
                       "[✓] Subtítulos guardados: {files}", "[✓] Sous-titres enregistrés : {files}",
                       "[✓] 字幕を保存しました：{files}"),

    # --- Unione con FFmpeg ---
    "log_merge_start": ("[*] Creazione del file MP4 finale con FFmpeg...", "[*] Creating the final MP4 file with FFmpeg...",
                        "[*] Creando el archivo MP4 final con FFmpeg...",
                        "[*] Création du fichier MP4 final avec FFmpeg...",
                        "[*] FFmpeg で最終的な MP4 ファイルを作成中..."),
    "log_many_segments": ("[*] Film lungo ({n} pezzi): li incollo prima in un file per traccia, poi unisco con FFmpeg.",
                          "[*] Long video ({n} segments): joining them into one file per track first, then merging "
                          "with FFmpeg.",
                          "[*] Vídeo largo ({n} segmentos): primero los uno en un archivo por pista y luego uno con "
                          "FFmpeg.",
                          "[*] Vidéo longue ({n} segments) : je les assemble d'abord en un fichier par piste, puis "
                          "je fusionne avec FFmpeg.",
                          "[*] 長い動画（{n} セグメント）：トラックごとに 1 つのファイルへ結合してから FFmpeg で統合します。"),
    "log_no_concatf": ("[*] Questa versione di FFmpeg non supporta «concatf» (serve la 6.0 o successiva): unisco i "
                       "segmenti prima di passarli a FFmpeg.",
                       "[*] This FFmpeg version does not support \"concatf\" (6.0 or later is needed): joining the "
                       "segments before passing them to FFmpeg.",
                       "[*] Esta versión de FFmpeg no admite «concatf» (hace falta la 6.0 o posterior): uno los "
                       "segmentos antes de pasárselos a FFmpeg.",
                       "[*] Cette version de FFmpeg ne prend pas en charge « concatf » (6.0 ou plus récente "
                       "nécessaire) : assemblage des segments avant de les passer à FFmpeg.",
                       "[*] この FFmpeg は「concatf」に対応していません（6.0 以降が必要）。セグメントを結合してから"
                       "FFmpeg に渡します。"),
    "err_merge_failed": ("Creazione del file MP4 non riuscita:\n\n{details}", "Creating the MP4 file failed:\n\n{details}",
                         "No se pudo crear el archivo MP4:\n\n{details}",
                         "La création du fichier MP4 a échoué :\n\n{details}",
                         "MP4 ファイルを作成できませんでした：\n\n{details}"),
    "err_ffmpeg_code": ("FFmpeg è terminato con il codice {code}", "FFmpeg exited with code {code}",
                        "FFmpeg terminó con el código {code}", "FFmpeg s'est arrêté avec le code {code}",
                        "FFmpeg がコード {code} で終了しました"),
    "err_move_failed": (
        "Il video è pronto ma non è stato possibile salvarlo come\n{path}\n(il file è forse aperto in un altro "
        "programma? {err}).\n\nIl video completo si trova in:\n{temp}",
        "The video is ready but could not be saved as\n{path}\n(is the file open in another program? {err}).\n\n"
        "The complete video is in:\n{temp}",
        "El vídeo está listo pero no se pudo guardar como\n{path}\n(¿está el archivo abierto en otro programa? "
        "{err}).\n\nEl vídeo completo está en:\n{temp}",
        "La vidéo est prête mais n'a pas pu être enregistrée sous\n{path}\n(le fichier est-il ouvert dans un autre "
        "programme ? {err}).\n\nLa vidéo complète se trouve dans :\n{temp}",
        "動画は完成しましたが、次の名前で保存できませんでした：\n{path}\n（ファイルが他のプログラムで開かれていませんか？ "
        "{err}）\n\n完成した動画の場所：\n{temp}"),
    "log_done": ("[✓] Operazione completata con successo! File salvato: {path}",
                 "[✓] Completed successfully! File saved: {path}",
                 "[✓] ¡Completado con éxito! Archivo guardado: {path}",
                 "[✓] Terminé avec succès ! Fichier enregistré : {path}",
                 "[✓] 正常に完了しました！保存先：{path}"),

    # --- Primo avvio ---
    "splash_title": ("Primo avvio: installazione delle librerie", "First start: installing libraries",
                     "Primer inicio: instalando bibliotecas", "Premier lancement : installation des bibliothèques",
                     "初回起動：ライブラリをインストール中"),
    "splash_body": ("{names}\nPuò richiedere qualche minuto…", "{names}\nThis may take a few minutes…",
                    "{names}\nPuede tardar unos minutos…", "{names}\nCela peut prendre quelques minutes…",
                    "{names}\n数分かかることがあります…"),
    "console_installing": ("[*] Installazione delle librerie mancanti: {names}...",
                           "[*] Installing missing libraries: {names}...",
                           "[*] Instalando las bibliotecas que faltan: {names}...",
                           "[*] Installation des bibliothèques manquantes : {names}...",
                           "[*] 不足しているライブラリをインストール中：{names}..."),
    "console_installed": ("[OK] Librerie installate.", "[OK] Libraries installed.", "[OK] Bibliotecas instaladas.",
                          "[OK] Bibliothèques installées.", "[OK] ライブラリをインストールしました。"),
    "install_interrupted": ("installazione interrotta", "installation interrupted", "instalación interrumpida",
                            "installation interrompue", "インストールが中断されました"),
    "dlg_install_failed_title": ("Installazione non riuscita", "Installation failed", "Instalación fallida",
                                 "Échec de l'installation", "インストールに失敗しました"),
    "dlg_install_failed_body": (
        "Non è stato possibile installare: {libs}.\n\nControlla la connessione e riprova, oppure esegui nel "
        "terminale:\n    python -m pip install {cmd}\n\n{output}",
        "Could not install: {libs}.\n\nCheck your connection and try again, or run in a terminal:\n"
        "    python -m pip install {cmd}\n\n{output}",
        "No se pudo instalar: {libs}.\n\nComprueba la conexión e inténtalo de nuevo, o ejecuta en el terminal:\n"
        "    python -m pip install {cmd}\n\n{output}",
        "Impossible d'installer : {libs}.\n\nVérifiez la connexion et réessayez, ou lancez dans un terminal :\n"
        "    python -m pip install {cmd}\n\n{output}",
        "インストールできませんでした：{libs}\n\n接続を確認してもう一度試すか、ターミナルで次を実行してください：\n"
        "    python -m pip install {cmd}\n\n{output}"),
}


def set_language(code: str):
    """Lingua dei testi dell'app (codice di LANGUAGES); quelle sconosciute tornano all'italiano."""
    global _language
    _language = code if code in LANGUAGES else "it"


def current_language() -> str:
    return _language


def tr(key: str, **kwargs) -> str:
    """Testo `key` nella lingua scelta, con i segnaposto riempiti da `kwargs`."""
    texts = TEXTS.get(key)
    text = texts[_LANGUAGE_INDEX[_language]] if texts else key
    return text.format(**kwargs) if kwargs else text


class DownloadCancelled(Exception):
    """Sollevata quando l'utente annulla l'operazione."""


class IncompleteDownload(Exception):
    """Il server continua a rifiutare i segmenti anche dopo diverse riprese."""


class TokenExpired(Exception):
    """Il server ha rifiutato una richiesta (401/403/410): serve un nuovo collegamento dalla pagina."""


class HttpStatusError(Exception):
    """Risposta HTTP di errore diversa da 401/403/410 (es. 404, 429, 503)."""

    def __init__(self, code: int, reason: str, retry_after: float | None = None):
        super().__init__(f"HTTP {code} {reason}".strip())
        self.code = code
        self.retry_after = retry_after  # Secondi suggeriti dal server prima di riprovare


# ============================================================
# IMPOSTAZIONI E UTILITÀ
# ============================================================
def load_settings() -> dict:
    try:
        return json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def save_settings(settings: dict):
    try:
        SETTINGS_FILE.write_text(json.dumps(settings, indent=2), encoding="utf-8")
    except OSError:
        pass


def sanitize_file_name(name: str) -> str:
    """Rimuove l'estensione .mp4 e i caratteri non ammessi nei nomi di file."""
    name = name.strip()
    if name.lower().endswith(".mp4"):
        name = name[:-4]
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", name)
    return name.strip(" .")


def remove_quietly(path: str):
    try:
        os.remove(path)
    except OSError:
        pass


def work_dir_for(output_file: str) -> str:
    return output_file + ".download"


def load_resume_state(output_file: str) -> dict | None:
    try:
        state = json.loads((Path(work_dir_for(output_file)) / "stato.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    if not isinstance(state, dict) or not state.get("page_url"):
        return None
    state.setdefault("position", 0.0)
    state.setdefault("duration", None)
    return state


def save_resume_state(output_file: str, state: dict):
    """Scrive stato.json in modo atomico: un'interruzione a metà non lascia un file illeggibile."""
    path = Path(work_dir_for(output_file)) / "stato.json"
    try:
        os.makedirs(path.parent, exist_ok=True)
        write_atomic(str(path), json.dumps(state, indent=2).encode("utf-8"))
    except OSError:
        pass


def write_atomic(path: str, data: bytes):
    """Il file compare con il nome definitivo solo quando è stato scritto per intero."""
    with open(path + ".tmp", "wb") as fh:
        fh.write(data)
    os.replace(path + ".tmp", path)


def has_segments(output_file: str) -> bool:
    """True se la cartella di lavoro contiene segmenti già scaricati."""
    try:
        return any(name.endswith(".ts") for name in os.listdir(work_dir_for(output_file)))
    except OSError:
        return False


def discard_partial(output_file: str):
    """Elimina la cartella dei segmenti creata dall'app per questo video."""
    work_dir = work_dir_for(output_file)
    if work_dir.endswith(".mp4.download") and os.path.isdir(work_dir):
        shutil.rmtree(work_dir, ignore_errors=True)


def same_page(url_a: str, url_b: str) -> bool:
    """Confronta due link ignorando il dominio (alcuni siti lo cambiano spesso)."""
    a, b = urllib.parse.urlsplit(url_a), urllib.parse.urlsplit(url_b)
    return (a.path.rstrip("/").lower(), a.query) == (b.path.rstrip("/").lower(), b.query)


def _fmt_time(seconds: float) -> str:
    """Posizione nel video, es. 01:02:03."""
    seconds = int(seconds)
    return f"{seconds // 3600:02d}:{seconds % 3600 // 60:02d}:{seconds % 60:02d}"


def iso639_2(language: str) -> str:
    """Codice lingua a tre lettere per i metadati, es. «it-IT» -> «ita»."""
    code = re.split(r"[-_]", language.strip().lower())[0]
    if re.fullmatch(r"[a-z]{3}", code):  # Solo lettere: il codice finisce anche nel nome dei file .srt
        return code
    return LANGUAGE_CODES.get(code, "und")


def describe_progress(state: dict) -> str:
    """Punto raggiunto da un download interrotto, es. «al 56%»."""
    if not state.get("position"):
        return tr("progress_start")
    if state.get("duration"):
        return tr("progress_percent", p=f"{min(state['position'] / state['duration'], 1.0):.0%}")
    return tr("progress_time", t=_fmt_time(state["position"]))


def _fmt_duration(seconds: float) -> str:
    """Durata leggibile, es. «3 min 12 s» o «1 h 05 min»."""
    seconds = int(round(seconds))
    if seconds < 60:
        return tr("dur_s", s=seconds)
    minutes, seconds = divmod(seconds, 60)
    if minutes < 60:
        return tr("dur_ms", m=minutes, s=seconds)
    hours, minutes = divmod(minutes, 60)
    return tr("dur_hm", h=hours, m=minutes)


def _fmt_bytes(value: float) -> str:
    for unit in ("B", "KB", "MB"):
        if value < 1024:
            return f"{value:.0f} {unit}" if unit != "MB" else f"{value:.1f} {unit}"
        value /= 1024
    return f"{value:.2f} GB"


# ============================================================
# RICERCA DEL BROWSER E DI FFMPEG
# ============================================================
SUPPORTED_BROWSERS = (
    {"exe": "brave", "name": "Brave", "win": r"BraveSoftware\Brave-Browser\Application\brave.exe",
     "mac": "Brave Browser", "linux": ("brave-browser", "brave-browser-stable", "brave")},
    {"exe": "chrome", "name": "Google Chrome", "win": r"Google\Chrome\Application\chrome.exe",
     "mac": "Google Chrome", "linux": ("google-chrome", "google-chrome-stable")},
    {"exe": "msedge", "name": "Microsoft Edge", "win": r"Microsoft\Edge\Application\msedge.exe",
     "mac": "Microsoft Edge", "linux": ("microsoft-edge", "microsoft-edge-stable")},
    {"exe": "vivaldi", "name": "Vivaldi", "win": r"Vivaldi\Application\vivaldi.exe",
     "mac": "Vivaldi", "linux": ("vivaldi", "vivaldi-stable")},
    {"exe": "chromium", "name": "Chromium", "win": None,
     "mac": "Chromium", "linux": ("chromium", "chromium-browser")},
)
UNSUPPORTED_BROWSER_NAMES = {
    "firefox": "Firefox", "opera": "Opera", "launcher": "Opera", "safari": "Safari",
    "librewolf": "LibreWolf", "waterfox": "Waterfox", "floorp": "Floorp", "zen": "Zen", "iexplore": "Internet Explorer",
}
MAC_BROWSER_BUNDLES = {
    "com.brave.browser": "Brave Browser", "com.google.chrome": "Google Chrome",
    "com.microsoft.edgemac": "Microsoft Edge", "com.vivaldi.vivaldi": "Vivaldi",
    "org.chromium.chromium": "Chromium", "org.mozilla.firefox": "Firefox", "com.apple.safari": "Safari",
}


def _identify_browser(path: str) -> dict | None:
    """Voce di SUPPORTED_BROWSERS corrispondente all'eseguibile, None se non è compatibile."""
    base = os.path.basename(path).lower()
    stem = base[:-4] if base.endswith(".exe") else base
    for browser in SUPPORTED_BROWSERS:
        if stem == browser["exe"] or base == browser["mac"].lower() or base in browser["linux"]:
            return browser
    return None


def browser_display_name(path: str) -> str:
    browser = _identify_browser(path)
    if browser:
        return browser["name"]
    stem = os.path.splitext(os.path.basename(path))[0]
    return UNSUPPORTED_BROWSER_NAMES.get(stem.lower(), stem)


def _windows_default_browser() -> str | None:
    import winreg
    base = r"Software\Microsoft\Windows\Shell\Associations\UrlAssociations"
    prog_id = None
    for subkey in (r"https\UserChoiceLatest\ProgId", r"https\UserChoice", r"http\UserChoiceLatest\ProgId", r"http\UserChoice"):
        try:
            with winreg.OpenKey(winreg.HKEY_CURRENT_USER, f"{base}\\{subkey}") as key:
                prog_id = winreg.QueryValueEx(key, "ProgId")[0]
        except OSError:
            continue
        if prog_id:
            break
    if not prog_id:
        return None
    with winreg.OpenKey(winreg.HKEY_CLASSES_ROOT, prog_id + r"\shell\open\command") as key:
        command = winreg.QueryValue(key, None).strip()
    if command.startswith('"'):
        return command[1:].split('"', 1)[0]
    match = re.match(r"(.+?\.exe)", command, re.IGNORECASE)
    return match.group(1) if match else command.split()[0]


def _mac_default_browser() -> str | None:
    import plistlib
    plist = Path.home() / "Library/Preferences/com.apple.LaunchServices/com.apple.launchservices.secure.plist"
    with open(plist, "rb") as fh:
        handlers = plistlib.load(fh).get("LSHandlers", [])
    bundle = next((h.get("LSHandlerRoleAll") for h in handlers if h.get("LSHandlerURLScheme") == "https"), None)
    app = MAC_BROWSER_BUNDLES.get((bundle or "").lower())
    return f"/Applications/{app}.app/Contents/MacOS/{app}" if app else None


def _linux_default_browser() -> str | None:
    desktop = subprocess.run(["xdg-settings", "get", "default-web-browser"], capture_output=True,
                             text=True, timeout=5).stdout.strip()
    folders = (Path.home() / ".local/share/applications", Path("/usr/share/applications"),
               Path("/var/lib/flatpak/exports/share/applications"))
    for folder in folders:
        desktop_file = folder / desktop
        if desktop and desktop_file.is_file():
            for line in desktop_file.read_text(errors="replace").splitlines():
                if line.startswith("Exec="):
                    executable = line[5:].split()[0]
                    return shutil.which(executable) or executable
    return None


def default_browser_path() -> str | None:
    """Eseguibile del browser predefinito del sistema (None se non rilevabile)."""
    try:
        if sys.platform == "win32":
            return _windows_default_browser()
        if sys.platform == "darwin":
            return _mac_default_browser()
        return _linux_default_browser()
    except (OSError, ValueError, subprocess.SubprocessError):
        return None


def _installed_browser_path(browser: dict) -> str | None:
    """Percorso di un browser compatibile se è installato."""
    candidates = []
    if sys.platform == "win32":
        import winreg
        for hive in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
            try:
                with winreg.OpenKey(hive, rf"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\{browser['exe']}.exe") as key:
                    candidates.append(winreg.QueryValue(key, None).strip('"'))
            except OSError:
                pass
        bases = [os.environ.get(v) for v in ("PROGRAMFILES", "PROGRAMFILES(X86)", "LOCALAPPDATA")]
        bases += [r"C:\Program Files", r"C:\Program Files (x86)"]
        for base in bases:
            if base and browser["win"]:
                candidates.append(os.path.join(base, browser["win"]))
    elif sys.platform == "darwin":
        app = browser["mac"]
        for folder in ("/Applications", os.path.expanduser("~/Applications")):
            candidates.append(f"{folder}/{app}.app/Contents/MacOS/{app}")
    else:
        candidates += [shutil.which(name) for name in browser["linux"]]
    return next((c for c in candidates if c and os.path.isfile(c)), None)


def detect_browser() -> dict | None:
    """Sceglie il browser da usare: il predefinito del PC se Playwright può controllarlo,
    altrimenti il primo browser compatibile installato. Restituisce {name, path, note} o None."""
    default = default_browser_path()
    if default and os.path.isfile(default) and _identify_browser(default):
        return {"name": browser_display_name(default), "path": default, "note": ("note_default", {})}
    if default:
        note = ("note_incompatible", {"name": browser_display_name(default)})
    else:
        note = ("note_not_detected", {})
    for browser in SUPPORTED_BROWSERS:
        path = _installed_browser_path(browser)
        if path:
            return {"name": browser["name"], "path": path, "note": note}
    return None


def find_ffmpeg() -> str | None:
    """Cerca FFmpeg nella cartella del programma, nel PATH e, su Windows, nelle cartelle di winget."""
    local_copy = Path(__file__).resolve().parent / ("ffmpeg.exe" if sys.platform == "win32" else "ffmpeg")
    if local_copy.is_file():
        return str(local_copy)
    found = shutil.which("ffmpeg")
    if found:
        return found
    local = os.environ.get("LOCALAPPDATA")
    if sys.platform == "win32" and local:
        patterns = (
            os.path.join(local, "Microsoft", "WinGet", "Links", "ffmpeg.exe"),
            os.path.join(local, "Microsoft", "WinGet", "Packages", "Gyan.FFmpeg*", "*", "bin", "ffmpeg.exe"),
        )
        for pattern in patterns:
            matches = glob.glob(pattern)
            if matches:
                return matches[0]
    return None


@functools.lru_cache(maxsize=None)
def ffmpeg_supports_concatf(ffmpeg_path: str) -> bool:
    """Il protocollo «concatf» esiste da FFmpeg 6.0: con versioni più vecchie si uniscono i segmenti a mano."""
    try:
        output = subprocess.run([ffmpeg_path, "-hide_banner", "-protocols"], capture_output=True, text=True,
                                errors="replace", timeout=15, creationflags=NO_WINDOW).stdout
    except (OSError, subprocess.SubprocessError):
        return False
    return re.search(r"^\s*concatf\s*$", output, re.MULTILINE) is not None


# ============================================================
# CONTROLLO VPN
# ============================================================
def _active_vpn_adapters() -> list[str]:
    """Restituisce le schede di rete attive che appartengono a un client VPN."""
    if sys.platform == "win32":
        script = (
            "[Console]::OutputEncoding = [Text.Encoding]::UTF8; "
            "Get-NetAdapter | Where-Object Status -eq 'Up' | "
            "ForEach-Object { $_.Name + ' (' + $_.InterfaceDescription + ')' }"
        )
        try:
            output = subprocess.run(
                ["powershell", "-NoProfile", "-NonInteractive", "-Command", script],
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=15, creationflags=NO_WINDOW,
            ).stdout
        except (OSError, subprocess.SubprocessError):
            return []
        adapters = [line.strip() for line in output.splitlines() if line.strip()]
        return [a for a in adapters if any(k in a.lower() for k in VPN_ADAPTER_KEYWORDS)]

    try:
        names = [name for _, name in socket.if_nameindex()]
    except (OSError, AttributeError):
        return []
    return [n for n in names if n.lower().startswith(VPN_INTERFACE_PREFIXES)]


class IpCheckUnavailable(Exception):
    """Nessun servizio per leggere l'IP pubblico ha risposto."""

    def __init__(self, errors: list[Exception]):
        super().__init__("; ".join(str(err) for err in errors))
        # Errore di DNS (es. «getaddrinfo failed»): il nome del servizio non viene risolto, tipico dei blocchi DNS
        self.dns_blocked = bool(errors) and all(
            isinstance(getattr(err, "reason", err), socket.gaierror) or "getaddrinfo" in str(err) for err in errors)


def _fetch_json(url: str) -> dict:
    request = urllib.request.Request(url, headers={"User-Agent": "hls-downloader", "Accept": "application/json"})
    with urllib.request.urlopen(request, timeout=6) as response:
        return json.load(response)


def _public_ip_info() -> dict:
    """IP pubblico, paese, provider e se l'indirizzo sembra di una VPN o di un datacenter ({ip, country, isp, flagged}).
    Prova più servizi: se uno è bloccato o non risponde passa al successivo; solleva IpCheckUnavailable se nessuno risponde."""
    errors: list[Exception] = []
    for kind, url in IP_CHECK_SERVICES:
        try:
            data = _fetch_json(url)
        except Exception as err:
            errors.append(err)
            continue
        if kind == "ip-api":
            if data.get("status") != "success":
                errors.append(RuntimeError(data.get("message") or tr("ip_invalid_response")))
                continue
            info = {"ip": data.get("query"), "country": data.get("country"), "isp": data.get("isp"),
                    "flagged": bool(data.get("proxy") or data.get("hosting"))}
        elif kind == "ipwhois":
            if data.get("success") is False:
                errors.append(RuntimeError(data.get("message") or tr("ip_invalid_response")))
                continue
            connection = data.get("connection") or {}
            info = {"ip": data.get("ip"), "country": data.get("country"),
                    "isp": connection.get("isp") or connection.get("org")}
        elif kind == "ipinfo":
            info = {"ip": data.get("ip"), "country": data.get("country"),
                    "isp": re.sub(r"^AS\d+\s+", "", data.get("org") or "")}
        else:
            info = {"ip": data.get("ip"), "country": "?", "isp": "?"}
        if not info.get("ip"):
            errors.append(RuntimeError(tr("ip_invalid_response")))
            continue
        if "flagged" not in info:
            isp = (info.get("isp") or "").lower()
            info["flagged"] = any(hint in isp for hint in DATACENTER_HINTS)
        return info
    raise IpCheckUnavailable(errors)


def check_vpn() -> dict:
    """Verifica se la connessione passa da una VPN.
    Restituisce {active, ip, country, isp, error, adapter}: il testo si compone con describe_vpn()."""
    adapters = _active_vpn_adapters()
    result = {"active": bool(adapters), "error": None, "adapter": adapters[0] if adapters else None}
    try:
        info = _public_ip_info()
    except IpCheckUnavailable as err:
        result["error"] = tr("vpn_ip_blocked") if err.dns_blocked else tr("vpn_ip_unverifiable", err=err)
    except Exception as err:
        result["error"] = tr("vpn_ip_unverifiable", err=err)
    else:
        result.update(ip=info["ip"], country=info.get("country"), isp=info.get("isp"))
        result["active"] = result["active"] or info["flagged"]
    return result


def describe_vpn(result: dict) -> str:
    """Dettagli del controllo VPN nella lingua scelta, es. «IP 1.2.3.4 · Italy · Fastweb»."""
    if result.get("error"):
        details = result["error"]  # Già tradotto da check_vpn()
    else:
        details = tr("vpn_ip", ip=result.get("ip"), country=result.get("country"), isp=result.get("isp"))
    if result.get("adapter"):
        details += tr("vpn_adapter", name=result["adapter"])
    return details


# ============================================================
# INTERCETTAZIONE DEL FLUSSO CON IL BROWSER
# ============================================================
async def _cancellable(awaitable, cancel_event: threading.Event, timeout: float | None = None):
    """Attende `awaitable` controllando se l'utente ha premuto Annulla; con `timeout` (secondi)
    solleva asyncio.TimeoutError se scade.

    `awaitable` viene subito trasformato in un task, così non resta mai una coroutine «non attesa»
    anche quando l'operazione viene annullata o va in timeout prima di partire; il task viene sempre
    chiuso (atteso dopo l'annullamento) per non lasciare attività in sospeso."""
    task = asyncio.ensure_future(awaitable)
    deadline = None if timeout is None else asyncio.get_running_loop().time() + timeout
    try:
        while not task.done():
            if cancel_event.is_set():
                raise DownloadCancelled()
            if deadline is not None and asyncio.get_running_loop().time() >= deadline:
                raise asyncio.TimeoutError()
            await asyncio.wait({task}, timeout=0.3)
        return task.result()
    finally:
        if not task.done():
            task.cancel()
            try:
                await task
            except (asyncio.CancelledError, Exception):
                pass


def _short_url(url: str) -> str:
    parts = urllib.parse.urlsplit(url)
    return f"{parts.netloc}{parts.path[:60]}"


def _same_site(host_a: str, host_b: str) -> bool:
    """True se due host appartengono allo stesso sito (stesso dominio o uno sottodominio dell'altro).
    Serve a distinguere la pagina del film dai domini pubblicitari su cui i popunder la dirottano."""
    a, b = host_a.lower().strip("."), host_b.lower().strip(".")
    if not a or not b:
        return True  # Nel dubbio non si blocca
    if a == b or a.endswith("." + b) or b.endswith("." + a):
        return True
    return a.split(".")[-2:] == b.split(".")[-2:]  # Stesse ultime due etichette (es. example.com)


async def intercept_hls_stream(page_url: str, browser_path: str, browser_name: str, log,
                               cancel_event: threading.Event) -> dict:
    """Apre il browser, simula la riproduzione e intercetta la playlist M3U8 del video con i relativi header."""
    candidates: dict[str, dict] = {}
    seen: set[str] = set()
    evaluations: set = set()
    client = HttpClient()
    captured_cookies: list = []
    main_found = asyncio.Event()
    stop_waiting = asyncio.Event()

    browser_segments: list[str] = []  # Diagnostica: come il browser chiede i pezzi del video
    # Pezzi già scaricati dal browser (URL -> byte): si riusano, perché alcuni server accettano
    # ogni indirizzo firmato una sola volta e una seconda richiesta verrebbe rifiutata con un 403.
    prefetched: dict[str, bytes] = {}
    prefetched_size = [0]

    async def evaluate(url: str, body: str, headers: dict, header_names: list[str]):
        request_headers = {name: value for name, value in headers.items() if value}
        if not client.cookies:  # Misurare una playlist principale richiede una richiesta: serve il cookie
            try:
                client.cookies = await context.cookies()
            except Exception:
                pass
        try:
            duration, is_master = await asyncio.to_thread(playlist_info, url, body, request_headers, client)
        except Exception as err:
            log(tr("log_stream_ignored", err=err, url=_short_url(url)))
            return
        # Il testo della playlist già scaricato dal browser viene riusato: alcuni server accettano
        # ogni indirizzo firmato una sola volta, e una seconda richiesta verrebbe rifiutata.
        candidates[url] = {"url": url, "headers": headers, "duration": duration, "master": is_master,
                           "body": body, "header_names": header_names}
        key = "log_stream_candidate_master" if is_master else "log_stream_candidate"
        log(tr(key, duration=_fmt_time(duration), url=_short_url(url)))
        if duration >= MIN_MAIN_DURATION:
            main_found.set()
            stop_waiting.set()
        else:
            log(tr("log_stream_short"))

    try:
        async with async_playwright() as p:
            log(tr("log_launch_browser", name=browser_name, path=browser_path))
            try:
                browser = await p.chromium.launch(
                    executable_path=browser_path,
                    headless=False,
                    args=BROWSER_ARGS,
                )
            except Exception as err:
                raise RuntimeError(tr("err_browser_launch", name=browser_name, path=browser_path, err=err)) from err
            browser.on("disconnected", lambda _: stop_waiting.set())

            try:
                context = await browser.new_context(viewport={"width": 1280, "height": 720})
                await context.add_init_script(WEBRTC_BLOCK_SCRIPT)
                await context.add_init_script(POPUP_BLOCK_SCRIPT)
                log(tr("log_incognito"))
                log(tr("log_webrtc_disabled"))
                log(tr("log_popups_blocked"))
                page = await context.new_page()
                page.on("close", lambda _: stop_waiting.set())

                # Chiude subito qualsiasi scheda/pop-up pubblicitario che riuscisse comunque ad aprirsi
                async def close_popup(popup):
                    if popup is page:
                        return
                    try:
                        await popup.close()
                    except Exception:
                        pass
                    log(tr("log_popup_closed"))

                context.on("page", lambda popup: asyncio.ensure_future(close_popup(popup)))

                # Impedisce ai popunder di dirottare la pagina del player su un sito pubblicitario
                # (è la causa del ricaricamento a ripetizione). Attivo solo finché non si trova il video.
                page_host = (urllib.parse.urlsplit(page_url).hostname or "").lower()

                async def guard_navigation(route):
                    request = route.request
                    try:
                        if (not main_found.is_set() and request.is_navigation_request()
                                and request.frame is page.main_frame and request.url != page.url):
                            host = (urllib.parse.urlsplit(request.url).hostname or "").lower()
                            if host and page_host and not _same_site(host, page_host):
                                # 204 «No Content»: il browser annulla il salto e resta sulla pagina del
                                # film (un abort la manderebbe invece su una pagina di errore di Chromium).
                                await route.fulfill(status=204, body="")
                                log(tr("log_ad_blocked", url=_short_url(request.url)))
                                return
                        await route.continue_()
                    except Exception:
                        try:
                            await route.continue_()
                        except Exception:
                            pass

                await page.route("**/*", guard_navigation)

                async def handle_response(response):
                    url = response.url
                    content_type = response.headers.get("content-type", "").lower()
                    is_m3u8 = (
                        ".m3u8" in url.lower()
                        or "mpegurl" in content_type
                        or "m3u8" in content_type
                    )
                    path = urllib.parse.urlsplit(url).path.lower()
                    if not is_m3u8 and (path.endswith((".ts", ".m4s", ".aac", ".m4a", ".mp4"))
                                        or "mp2t" in content_type):
                        if len(browser_segments) < 2:
                            browser_segments.append(f"{_scrub_url(url)} → {response.status}")  # Diagnostica
                        if response.status == 200 and url not in prefetched and prefetched_size[0] < 200_000_000:
                            try:
                                data = await response.body()
                            except Exception:
                                return
                            prefetched[url] = data
                            prefetched_size[0] += len(data)
                        return
                    if not is_m3u8 or url in seen:
                        return
                    seen.add(url)
                    try:
                        body = await response.text()
                        request_headers = await response.request.all_headers()
                    except Exception:
                        return
                    headers = {
                        "User-Agent": request_headers.get("user-agent", ""),
                        "Referer": request_headers.get("referer", page.url),
                        "Origin": request_headers.get("origin", ""),
                    }
                    names = sorted(name for name in request_headers if not name.startswith(":"))
                    task = asyncio.ensure_future(evaluate(url, body, headers, names))
                    evaluations.add(task)
                    task.add_done_callback(evaluations.discard)

                page.on("response", handle_response)

                log(tr("log_navigating", url=page_url))
                try:
                    await _cancellable(page.goto(page_url, wait_until="domcontentloaded", timeout=30000), cancel_event)
                except DownloadCancelled:
                    raise
                except Exception as e:
                    log(tr("log_page_warning", err=e))

                log(tr("log_searching_player"))
                await _cancellable(asyncio.sleep(3), cancel_event)

                async def nudge_play():
                    """Avvia la riproduzione cliccando il video (nella pagina o in un iframe del player);
                    in mancanza clicca al centro. I pop-up sono già bloccati, quindi il clic non apre nulla."""
                    for frame in page.frames:
                        try:
                            video = frame.locator("video").first
                            if await video.count() and await video.is_visible():
                                await video.scroll_into_view_if_needed(timeout=1500)
                                await video.click(force=True, timeout=2000)
                                return
                        except Exception:
                            pass
                    try:
                        await page.mouse.click(640, 360)
                    except Exception:
                        pass

                if not main_found.is_set():
                    log(tr("log_waiting_stream", seconds=TIMEOUT_PLAYWRIGHT))
                # Ridà «Play» ogni paio di secondi (il primo clic spesso chiude solo un overlay, il
                # secondo avvia davvero il video) mentre aspetta il flusso, fino al timeout complessivo.
                deadline = time.monotonic() + TIMEOUT_PLAYWRIGHT
                while not main_found.is_set() and not cancel_event.is_set() and time.monotonic() < deadline:
                    await nudge_play()
                    try:
                        await _cancellable(stop_waiting.wait(), cancel_event, timeout=2.0)
                    except asyncio.TimeoutError:
                        pass
                if cancel_event.is_set():
                    raise DownloadCancelled()
                if main_found.is_set():
                    await _cancellable(asyncio.sleep(2), cancel_event)
                if evaluations:
                    await asyncio.wait(set(evaluations), timeout=15)
                # Cookie ottenuti dal browser (incluso il «lasciapassare» cf_clearance di Cloudflare):
                # servono al download dei segmenti, altrimenti il server li rifiuta con un 403.
                try:
                    captured_cookies.extend(await context.cookies())
                except Exception:
                    pass
            finally:
                if browser.is_connected():
                    await browser.close()
    finally:
        client.close()

    if not candidates:
        log(tr("log_timeout_stream"))
        return {}
    best = max(candidates.values(), key=lambda c: (round(c["duration"] / 30), c["master"]))
    if best["duration"] < MIN_MAIN_DURATION:
        log(tr("log_stream_too_short", duration=_fmt_time(best["duration"])))
    log(tr("log_stream_chosen", duration=_fmt_time(best["duration"]), url=best["url"]))
    if captured_cookies:
        log(tr("log_cookies", n=len(captured_cookies)))
    # Diagnostica per i 403: cosa ha inviato il browser e come ha chiesto i pezzi del video
    log(tr("log_browser_headers", names=", ".join(best["header_names"]) or "?"))
    for segment in browser_segments:
        log(tr("log_browser_segment", info=segment))
    if not browser_segments:
        log(tr("log_browser_no_segments"))
    return {"m3u8_url": best["url"], "headers": best["headers"], "cookies": captured_cookies,
            "prefetched": prefetched,
            "body": best["body"]}


# ============================================================
# DOWNLOAD HLS: SEGMENTI IN PARALLELO CON RIPRESA
# ============================================================
def _scrub_url(url: str) -> str:
    """Host e percorso dell'URL con i soli nomi dei parametri (i valori, es. i token, non finiscono nel registro)."""
    parts = urllib.parse.urlsplit(url)
    names = [name for name, _ in urllib.parse.parse_qsl(parts.query, keep_blank_values=True)]
    return f"{parts.netloc}{parts.path}" + (f"?{','.join(names)}" if names else "")


def _refusal_details(response: http.client.HTTPResponse, body: bytes, url: str) -> str:
    """Chi ha rifiutato la richiesta: utile a capire se è Cloudflare o il controllo del server video."""
    server = response.getheader("Server", "?")
    cloudflare = "sì" if response.getheader("CF-Ray") or "cloudflare" in server.lower() else "no"
    snippet = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", body[:400].decode("utf-8", "replace"))).strip()[:90]
    return f"{_scrub_url(url)} · server={server} · cloudflare={cloudflare} · «{snippet}»"


def _retry_after(response: http.client.HTTPResponse) -> float | None:
    value = response.getheader("Retry-After", "")
    return float(value) if value.strip().isdigit() else None


class HttpClient:
    """Client HTTP(S) con connessioni persistenti (keep-alive) e gestione avanzata delle regole di proxy bypass."""

    def __init__(self, timeout: float = HTTP_TIMEOUT, cookies: list | None = None):
        self.timeout = timeout
        self.ssl_context = ssl.create_default_context()
        self.local = threading.local()
        self.lock = threading.Lock()
        self.connections: list[http.client.HTTPConnection] = []
        self.aborted = False
        self.cookies = cookies or []  # Cookie del browser (es. cf_clearance di Cloudflare), per host
        try:
            self.proxies = urllib.request.getproxies()
        except Exception:
            self.proxies = {}

    def _cookie_header(self, url: str) -> str | None:
        """Intestazione Cookie coi cookie del browser validi per l'host e il percorso dell'URL."""
        if not self.cookies:
            return None
        parts = urllib.parse.urlsplit(url)
        host = (parts.hostname or "").lower()
        path = parts.path or "/"
        jar = []
        for cookie in self.cookies:
            domain = (cookie.get("domain") or "").lower().lstrip(".")
            cpath = cookie.get("path") or "/"
            if domain and (host == domain or host.endswith("." + domain)) and path.startswith(cpath):
                jar.append(f"{cookie['name']}={cookie['value']}")
        return "; ".join(jar) if jar else None

    def get(self, url: str, headers: dict, byte_range: tuple[int, int] | None = None) -> bytes:
        """Scarica `url`; solleva TokenExpired se il server nega l'accesso."""
        request_headers = {"Accept": "*/*", "Accept-Encoding": "identity", **headers}
        if byte_range:
            start, length = byte_range
            request_headers["Range"] = f"bytes={start}-{start + length - 1}"
        caller_cookie = any(name.lower() == "cookie" for name in headers)  # Cookie già fornito a mano
        for _ in range(MAX_REDIRECTS + 1):
            if self.cookies and not caller_cookie:  # Ricalcolato per host a ogni redirect
                cookie = self._cookie_header(url)
                request_headers.pop("Cookie", None)
                if cookie:
                    request_headers["Cookie"] = cookie
            response, body = self._request(url, request_headers)
            location = response.getheader("Location")
            if response.status in (301, 302, 303, 307, 308) and location:
                url = urllib.parse.urljoin(url, location)
                continue
            if response.status in (401, 403, 410):
                raise TokenExpired(f"HTTP {response.status} {response.reason} · {_refusal_details(response, body, url)}")
            if response.status >= 400:
                raise HttpStatusError(response.status, response.reason, _retry_after(response))
            if byte_range and response.status == 200:
                body = body[byte_range[0]:byte_range[0] + byte_range[1]]
            return body
        raise HttpStatusError(310, tr("err_too_many_redirects"))

    def _request(self, url: str, headers: dict) -> tuple[http.client.HTTPResponse, bytes]:
        parts = urllib.parse.urlsplit(url)
        if parts.scheme not in ("http", "https") or not parts.hostname:
            raise ValueError(tr("err_invalid_address", url=url))
        key = (parts.scheme, parts.hostname, parts.port)
        path = urllib.parse.urlunsplit(("", "", parts.path or "/", parts.query, ""))
        for attempt in range(2):
            if self.aborted:
                raise ConnectionAbortedError(tr("err_aborted"))
            entry, reused = self._connection(key)
            target = url if entry["absolute"] else path
            try:
                entry["conn"].request("GET", target, headers={**headers, **entry["extra"]})
                response = entry["conn"].getresponse()
                body = response.read()
            except (http.client.HTTPException, OSError):
                self._drop(key)
                if reused and attempt == 0 and not self.aborted:
                    continue
                raise
            if response.will_close:
                self._drop(key)
            return response, body
        raise ConnectionError(tr("err_no_connection"))

    def _should_bypass(self, host: str) -> bool:
        """Verifica se l'host deve bypassare il proxy (localhost/loopback, regole d'ambiente NO_PROXY o del sistema)."""
        if host in ("localhost", "127.0.0.1", "::1"):
            return True
        no_proxy = os.environ.get("no_proxy") or os.environ.get("NO_PROXY")
        if no_proxy:
            return urllib.request.proxy_bypass_environment(host)
        return urllib.request.proxy_bypass(host)

    def _connection(self, key: tuple) -> tuple[dict, bool]:
        """Connessione del thread corrente verso il server indicato; True se era già stata usata."""
        pool = getattr(self.local, "pool", None)
        if pool is None:
            pool = self.local.pool = {}
        if key in pool:
            return pool[key], True

        scheme, host, port = key
        proxy = self._proxy_for(scheme, host)
        extra, absolute = {}, False
        if proxy:
            auth = {}
            if proxy.username:
                credentials = f"{urllib.parse.unquote(proxy.username)}:{urllib.parse.unquote(proxy.password or '')}"
                auth = {"Proxy-Authorization": "Basic " + base64.b64encode(credentials.encode()).decode()}
            if scheme == "https":
                conn = http.client.HTTPSConnection(proxy.hostname, proxy.port, timeout=self.timeout,
                                                   context=self.ssl_context)
                conn.set_tunnel(host, port or 443, headers=auth)
            else:
                conn = http.client.HTTPConnection(proxy.hostname, proxy.port, timeout=self.timeout)
                extra, absolute = auth, True
        elif scheme == "https":
            conn = http.client.HTTPSConnection(host, port, timeout=self.timeout, context=self.ssl_context)
        else:
            conn = http.client.HTTPConnection(host, port, timeout=self.timeout)

        entry = pool[key] = {"conn": conn, "extra": extra, "absolute": absolute}
        with self.lock:
            self.connections.append(conn)
        return entry, False

    def _proxy_for(self, scheme: str, host: str):
        proxy = self.proxies.get(scheme)
        if not proxy:
            return None
        try:
            if self._should_bypass(host):
                return None
        except Exception:
            pass
        parsed = urllib.parse.urlsplit(proxy if "://" in proxy else "http://" + proxy)
        return parsed if parsed.hostname else None

    def _drop(self, key: tuple):
        entry = getattr(self.local, "pool", {}).pop(key, None)
        if entry:
            entry["conn"].close()
            with self.lock:
                if entry["conn"] in self.connections:
                    self.connections.remove(entry["conn"])

    def abort(self):
        """Interrompe subito le richieste in corso negli altri thread."""
        self.aborted = True
        with self.lock:
            connections = list(self.connections)
        for conn in connections:
            sock = conn.sock
            if sock is None:
                continue
            try:
                sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
            try:
                socket.close(sock.detach())
            except OSError:
                pass

    def close(self):
        """Chiude tutte le connessioni."""
        with self.lock:
            connections, self.connections = self.connections, []
        for conn in connections:
            conn.close()


def _parse_attributes(text: str) -> dict:
    """Attributi di un tag M3U8, es. TYPE=AUDIO,NAME="Italiano"."""
    return {m.group(1): m.group(2).strip('"') for m in re.finditer(r'([A-Z0-9-]+)=("[^"]*"|[^,]*)', text)}


def _parse_byte_range(value: str, next_offset: int = 0) -> tuple[int, int]:
    """«lunghezza[@inizio]» -> (inizio, lunghezza)."""
    length, _, offset = value.partition("@")
    return (int(offset) if offset else next_offset, int(length))


def _parse_media_playlist(text: str, base_url: str) -> dict:
    """Elenco dei segmenti di una playlist (durata, cifratura, eventuale byte-range)."""
    segments, key, init = [], None, None
    sequence, duration, byte_range, next_offset = 0, 0.0, None, 0
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("#EXT-X-MEDIA-SEQUENCE:"):
            sequence = int(line.split(":", 1)[1])
        elif line.startswith("#EXT-X-KEY:"):
            attrs = _parse_attributes(line.split(":", 1)[1])
            method = attrs.get("METHOD", "NONE").upper()
            if method == "NONE":
                key = None
            elif method == "AES-128":
                if not attrs.get("URI"):
                    raise RuntimeError(tr("err_aes_no_uri"))
                key = {"url": urllib.parse.urljoin(base_url, attrs["URI"]), "iv": attrs.get("IV")}
            else:
                raise RuntimeError(tr("err_unsupported_protection", method=method))
        elif line.startswith("#EXT-X-MAP:"):
            attrs = _parse_attributes(line.split(":", 1)[1])
            init = {"url": urllib.parse.urljoin(base_url, attrs["URI"]), "key": None,
                    "range": _parse_byte_range(attrs["BYTERANGE"]) if attrs.get("BYTERANGE") else None}
        elif line.startswith("#EXTINF:"):
            duration = float(line.split(":", 1)[1].split(",")[0] or 0)
        elif line.startswith("#EXT-X-BYTERANGE:"):
            byte_range = _parse_byte_range(line.split(":", 1)[1], next_offset)
            next_offset = byte_range[0] + byte_range[1]
        elif line and not line.startswith("#"):
            segments.append({
                "url": urllib.parse.urljoin(base_url, line),
                "duration": duration,
                "key": key,
                "sequence": sequence + len(segments),
                "range": byte_range,
            })
            duration, byte_range = 0.0, None
    if not segments:
        raise RuntimeError(tr("err_no_segments"))
    return {"segments": segments, "init": init}


def _variant_quality(variant: dict) -> tuple[int, int]:
    """Risoluzione (pixel) e banda di una variante: la più alta è la qualità migliore."""
    width, _, height = variant["attrs"].get("RESOLUTION", "0x0").partition("x")
    return int(width or 0) * int(height or 0), int(variant["attrs"].get("BANDWIDTH", 0) or 0)


def _playlist_duration(text: str) -> float:
    """Durata totale (secondi) di una playlist di segmenti."""
    durations = [float(line.split(":", 1)[1].split(",")[0] or 0)
                 for line in (raw.strip() for raw in text.splitlines()) if line.startswith("#EXTINF:")]
    if not durations:
        raise RuntimeError(tr("err_not_video_playlist"))
    return sum(durations)


def playlist_info(url: str, body: str, headers: dict, client: HttpClient) -> tuple[float, bool]:
    """Durata del video di una playlist intercettata e se è una playlist principale (con varianti).
    Per una playlist principale si misura la variante di qualità migliore."""
    if "#EXT-X-STREAM-INF" not in body:
        return _playlist_duration(body), False
    lines = [line.strip() for line in body.splitlines()]
    variants = []
    for i, line in enumerate(lines):
        if line.startswith("#EXT-X-STREAM-INF:"):
            uri = next((l for l in lines[i + 1:] if l and not l.startswith("#")), None)
            if uri:
                variants.append({"attrs": _parse_attributes(line.split(":", 1)[1]),
                                 "url": urllib.parse.urljoin(url, uri)})
    if not variants:
        raise RuntimeError(tr("err_no_variants"))
    media = client.get(max(variants, key=_variant_quality)["url"], headers).decode("utf-8", "replace")
    return _playlist_duration(media), True


def resolve_tracks(m3u8_url: str, headers: dict, client: HttpClient,
                   prefer_video: str = "", body: str | None = None) -> tuple[list[dict], list[dict]]:
    """Legge la playlist intercettata e sceglie le tracce: video alla qualità migliore (o alla
    risoluzione `prefer_video`, se è una ripresa) e tutte le lingue audio, italiano per primo.
    `body` è il testo della playlist già scaricato dal browser: se c'è non la si richiede di nuovo.
    Restituisce (tracce con l'elenco dei segmenti, sottotitoli disponibili)."""
    text = body if body else client.get(m3u8_url, headers).decode("utf-8", "replace")
    if "#EXT-X-STREAM-INF" not in text:  # Playlist semplice: un'unica traccia
        track = {"id": "video", "kind": "video", "label": "", "language": "", **_parse_media_playlist(text, m3u8_url)}
        return [track], []

    variants, audio_media, subtitle_media = [], [], []
    lines = [line.strip() for line in text.splitlines()]
    for i, line in enumerate(lines):
        if line.startswith("#EXT-X-STREAM-INF:"):
            uri = next((l for l in lines[i + 1:] if l and not l.startswith("#")), None)
            if uri:
                variants.append({"attrs": _parse_attributes(line.split(":", 1)[1]),
                                 "url": urllib.parse.urljoin(m3u8_url, uri)})
        elif line.startswith("#EXT-X-MEDIA:"):
            attrs = _parse_attributes(line.split(":", 1)[1])
            if attrs.get("URI") and attrs.get("TYPE") in ("AUDIO", "SUBTITLES"):
                attrs["url"] = urllib.parse.urljoin(m3u8_url, attrs["URI"])
                (audio_media if attrs["TYPE"] == "AUDIO" else subtitle_media).append(attrs)
    if not variants:
        raise RuntimeError(tr("err_no_variants"))

    same_resolution = [v for v in variants if prefer_video and v["attrs"].get("RESOLUTION", "") == prefer_video]
    best = max(same_resolution or variants, key=_variant_quality)
    tracks = [{"id": "video", "kind": "video", "url": best["url"], "label": best["attrs"].get("RESOLUTION", ""),
               "language": ""}]
    audios = [m for m in audio_media if m.get("GROUP-ID") == best["attrs"].get("AUDIO")]
    audios.sort(key=lambda m: (not m.get("LANGUAGE", "").lower().startswith("it"), m.get("DEFAULT") != "YES"))
    seen = set()
    for audio in audios:
        if audio["url"] not in seen:
            seen.add(audio["url"])
            tracks.append({"id": f"audio{len(seen)}", "kind": "audio", "url": audio["url"],
                           "label": audio.get("NAME", ""), "language": audio.get("LANGUAGE", "")})

    subtitles, seen = [], set()
    for sub in subtitle_media:
        if sub.get("GROUP-ID") == best["attrs"].get("SUBTITLES") and sub["url"] not in seen:
            seen.add(sub["url"])
            subtitles.append({"id": f"sub{len(seen)}", "url": sub["url"], "label": sub.get("NAME", ""),
                              "language": sub.get("LANGUAGE", ""), "forced": sub.get("FORCED") == "YES"})

    for track in tracks:
        playlist = client.get(track["url"], headers).decode("utf-8", "replace")
        track.update(_parse_media_playlist(playlist, track["url"]))
    return tracks, subtitles


def track_signature(tracks: list[dict]) -> list[dict]:
    """Descrizione delle tracce scelte: alla ripresa deve coincidere, altrimenti i segmenti già
    scaricati appartengono a un'altra versione del video e mescolarli rovinerebbe il file."""
    return [{"id": t["id"], "label": t["label"], "language": t["language"],
             "segments": len(t["segments"]), "init": bool(t.get("init"))} for t in tracks]


def describe_tracks(signature: list[dict]) -> str:
    video = signature[0]
    audio = ", ".join(t["label"] or t["language"] or t["id"] for t in signature[1:])
    text = tr("tracks_desc", video=video["label"] or "?", segments=video["segments"])
    return text + (tr("tracks_desc_audio", audio=audio) if audio else "")


class SegmentDownloader:
    """Scarica i segmenti delle tracce in parallelo e li decifra.

    Ogni segmento è salvato come file a sé nella cartella di lavoro: se il server smette di
    rispondere (403) basta un nuovo collegamento per scaricare solo quelli mancanti.
    """

    def __init__(self, work_dir: str, client: HttpClient, headers: dict, log, progress,
                 cancel_event: threading.Event, workers: int = SEGMENT_WORKERS,
                 prefetched: dict[str, bytes] | None = None):
        self.work_dir = work_dir
        self.client = client
        self.headers = headers
        self.prefetched = dict(prefetched or {})  # Pezzi già scaricati dal browser (URL -> byte)
        self.reused = 0
        self.refused = 0  # Pezzi rifiutati (403) in questa sessione: si recuperano con un collegamento nuovo
        self.log = log
        self.progress = progress
        self.cancel_event = cancel_event
        self.workers = max(1, workers)
        self.stop = threading.Event()  # Collegamento scaduto o errore: gli altri segmenti si fermano
        self.expired = False
        self.lock = threading.Lock()
        self.key_lock = threading.Lock()
        self.keys: dict[str, bytes] = {}
        self.new_segments = 0
        self.done_units = self.total_units = self.total_video = 0.0
        self.bytes = 0
        self.started = self.last_report = 0.0
        self.last_stats: dict | None = None

    def segment_path(self, track: dict, index: int) -> str:
        return os.path.join(self.work_dir, f"{track['id']}_{index:05d}.ts")

    def run(self, tracks: list[dict]) -> bool:
        """Scarica i segmenti mancanti. Restituisce True a download completo, False se annullato;
        solleva TokenExpired se il server ha smesso di accettare il collegamento."""
        os.makedirs(self.work_dir, exist_ok=True)
        for track in tracks:
            if track.get("init"):
                init_path = os.path.join(self.work_dir, f"{track['id']}_init.mp4")
                if not os.path.exists(init_path):
                    try:
                        data = self._get(track["init"], tr("what_init", track=track["id"]))
                    except TokenExpired as err:
                        self.log(tr("log_track_refused", track=track["id"], err=err))
                        self.expired = True
                        raise
                    if data is None:
                        return False
                    write_atomic(init_path, data)

        self.total_video = sum(s["duration"] for s in tracks[0]["segments"]) or 1.0
        self.total_units = sum(s["duration"] for t in tracks for s in t["segments"]) or 1.0
        pending = []
        for track in tracks:
            for index, segment in enumerate(track["segments"]):
                path = self.segment_path(track, index)
                if os.path.exists(path):
                    self.done_units += segment["duration"]
                    self.bytes += os.path.getsize(path)
                else:
                    pending.append((index, track, segment))
        pending.sort(key=lambda item: item[0])  # Video e audio avanzano insieme

        self.started = time.monotonic()
        self._report(force=True)
        errors = []
        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            remaining = {pool.submit(self._fetch, track, index, segment) for index, track, segment in pending}
            aborted = False
            while remaining:
                done, remaining = wait_futures(remaining, timeout=0.5, return_when=FIRST_COMPLETED)
                for future in done:
                    try:
                        future.result()
                    except Exception as err:
                        errors.append(err)
                        self.stop.set()
                if not aborted and (self.cancel_event.is_set() or self.stop.is_set()):
                    aborted = True
                    self.client.abort()  # Non si aspetta la fine delle richieste in corso
        self._report(force=True)

        if self.cancel_event.is_set():
            return False
        if self.expired or self.refused:  # Pezzi mancanti: serve un collegamento nuovo per recuperarli
            if self.refused and not self.expired:
                self.log(tr("log_refused_missing", n=self.refused))
                self.expired = True  # Già spiegato nel registro: niente altri messaggi di rifiuto
            raise TokenExpired()
        if errors:
            raise errors[0]
        return True

    def _halted(self) -> bool:
        return self.cancel_event.is_set() or self.stop.is_set()

    def _get(self, segment: dict, what: str) -> bytes | None:
        """Scarica (e decifra) un segmento ripetendo i tentativi; None se il download si è fermato."""
        for attempt in range(SEGMENT_RETRIES):
            if self._halted():
                return None
            try:
                with self.lock:  # Pezzo già scaricato dal browser: non lo si richiede (indirizzo monouso)
                    data = None if segment.get("range") else self.prefetched.pop(segment["url"], None)
                    if data is not None:
                        self.reused += 1
                if data is None:
                    data = self.client.get(segment["url"], self.headers, segment.get("range"))
                if segment.get("key"):
                    data = self._decrypt(data, segment)
                return data
            except TokenExpired:
                raise
            except (HttpStatusError, http.client.HTTPException, OSError, ValueError) as err:
                if self._halted():
                    return None
                if attempt == SEGMENT_RETRIES - 1:
                    raise RuntimeError(tr("err_download_failed", what=what, err=err)) from err
                delay = min(getattr(err, "retry_after", None) or 2 * (attempt + 1), 30)
                self.log(tr("log_retry", what=what[0].upper() + what[1:], err=err, delay=f"{delay:.0f}"))
                if self.cancel_event.wait(delay):
                    return None
        return None

    def _fetch(self, track: dict, index: int, segment: dict):
        try:
            data = self._get(segment, tr("what_segment", n=index + 1, track=track["id"]))
        except TokenExpired as err:
            with self.lock:
                self.refused += 1
                if self.refused == 1:
                    self.log(tr("log_segment_refused", n=index + 1, err=err))
                    self.log(tr("log_refusal_stats", ok=self.new_segments, reused=self.reused))
                # Se gli altri pezzi arrivano, quello rifiutato si recupera dopo con un collegamento nuovo
                # (es. indirizzo monouso già consumato da un tentativo interrotto). Ci si ferma subito solo
                # se i rifiuti arrivano senza che il server accetti nessuna richiesta dell'app.
                own_successes = self.new_segments - self.reused
                if own_successes <= 0 and self.refused >= min(3, self.workers):
                    self.expired = True
                    halt = True
                else:
                    halt = False
            if halt:
                self.stop.set()
            return
        if data is None:
            return
        write_atomic(self.segment_path(track, index), data)
        with self.lock:
            self.done_units += segment["duration"]
            self.bytes += len(data)
            self.new_segments += 1
        self._report()

    def _decrypt(self, data: bytes, segment: dict) -> bytes:
        key = segment["key"]
        with self.key_lock:
            if key["url"] not in self.keys:
                key_bytes = self.client.get(key["url"], self.headers)
                if len(key_bytes) != 16:  # Es. pagina di errore al posto della chiave: non va memorizzata
                    raise ValueError(tr("err_bad_key", n=len(key_bytes)))
                self.keys[key["url"]] = key_bytes
            key_bytes = self.keys[key["url"]]
        if key["iv"]:
            iv = bytes.fromhex(key["iv"][2:] if key["iv"].lower().startswith("0x") else key["iv"])
        else:
            iv = segment["sequence"].to_bytes(16, "big")  # Default HLS: numero del segmento
        if len(data) % 16:
            raise ValueError(tr("err_incomplete_encrypted"))
        plain = AES.new(key_bytes, AES.MODE_CBC, iv).decrypt(data)
        padding = plain[-1] if plain else 0
        if 1 <= padding <= 16 and plain.endswith(bytes([padding]) * padding):
            plain = plain[:-padding]
        return plain

    def _report(self, force: bool = False):
        now = time.monotonic()
        with self.lock:
            if not force and now - self.last_report < 0.3:
                return
            self.last_report = now
            fraction = min(self.done_units / self.total_units, 1.0)
            self.last_stats = {
                "position": fraction * self.total_video,  # Secondi di video equivalenti
                "duration": self.total_video,
                "bytes": self.bytes,
                "wall": now - self.started,
            }
        self.progress(self.last_stats)


# ============================================================
# SOTTOTITOLI
# ============================================================
VTT_TIME = re.compile(r"(?:(\d+):)?(\d{1,2}):(\d{2})[.,](\d{1,3})")
VTT_TAGS = re.compile(r"</?(?!/?(?:i|b|u)>)[^>]*>")  # Toglie i tag WebVTT tranne corsivo, grassetto, sottolineato


def _srt_time(text: str) -> str | None:
    match = VTT_TIME.fullmatch(text.strip())
    if not match:
        return None
    hours, minutes, seconds, millis = match.groups()
    return f"{int(hours or 0):02d}:{int(minutes):02d}:{int(seconds):02d},{millis.ljust(3, '0')}"


def webvtt_to_srt(parts: list[str]) -> str:
    """Unisce i pezzi di un sottotitolo WebVTT in un unico file SRT (togliendo i doppioni)."""
    cues, seen = [], set()
    for text in parts:
        text = text.lstrip("﻿").replace("\r\n", "\n").replace("\r", "\n")
        for block in re.split(r"\n\s*\n", text):
            lines = block.strip("\n").split("\n")
            timing = next((i for i, line in enumerate(lines) if "-->" in line), None)
            if timing is None:
                continue  # Intestazione WEBVTT, NOTE, STYLE...
            start, _, end = lines[timing].partition("-->")
            start, end = _srt_time(start), _srt_time(end.split()[0] if end.split() else "")
            body = "\n".join(VTT_TAGS.sub("", line) for line in lines[timing + 1:]).strip()
            if start and end and body and (start, end, body) not in seen:
                seen.add((start, end, body))
                cues.append((start, end, body))
    cues.sort(key=lambda cue: cue[0])
    return "".join(f"{n}\n{start} --> {end}\n{body}\n\n" for n, (start, end, body) in enumerate(cues, start=1))


def download_subtitles(client: HttpClient, headers: dict, subtitles: list[dict], work_dir: str, log,
                       cancel_event: threading.Event) -> list[dict]:
    """Scarica i sottotitoli e li converte in SRT nella cartella di lavoro.
    Un errore sui sottotitoli non ferma il download del video."""
    saved = []
    for sub in subtitles:
        if cancel_event.is_set():
            break
        name = sub["label"] or sub["language"] or sub["id"]
        path = os.path.join(work_dir, f"{sub['id']}.srt")
        if not os.path.exists(path):
            try:
                playlist = client.get(sub["url"], headers).decode("utf-8-sig", "replace")
                if playlist.lstrip().startswith("WEBVTT"):  # File unico invece di una playlist
                    parts = [playlist]
                else:
                    segments = _parse_media_playlist(playlist, sub["url"])["segments"]
                    if any(s["key"] for s in segments):
                        raise RuntimeError(tr("err_subs_encrypted"))
                    parts = [client.get(s["url"], headers, s["range"]).decode("utf-8-sig", "replace")
                             for s in segments]
                srt = webvtt_to_srt(parts)
                if not srt:
                    raise RuntimeError(tr("err_subs_empty"))
                write_atomic(path, srt.encode("utf-8"))
            except Exception as err:
                log(tr("log_subs_failed", name=name, err=err))
                continue
        log(tr("log_subs_ok", name=name))
        saved.append({**sub, "path": path})
    return saved


def save_subtitles(subtitles: list[dict], output_file: str, log) -> list[str]:
    """Copia i sottotitoli accanto al video con lo stesso nome (es. film.ita.srt), così i lettori li caricano da soli."""
    base, used, saved = os.path.splitext(output_file)[0], set(), []
    for sub in subtitles:
        suffix = iso639_2(sub["language"]) if sub["language"] else sub["id"]
        if sub["forced"]:
            suffix += ".forced"
        if suffix in used:
            suffix += f".{sub['id']}"
        used.add(suffix)
        target = f"{base}.{suffix}.srt"
        try:
            shutil.copyfile(sub["path"], target)
            saved.append(target)
        except OSError as err:
            log(tr("log_subs_save_failed", path=target, err=err))
    if saved:
        log(tr("log_subs_saved", files=", ".join(os.path.basename(p) for p in saved)))
    return saved


# ============================================================
# UNIONE CON FFMPEG
# ============================================================
def segment_files(track: dict) -> list[str]:
    """Nomi dei file di una traccia nella cartella di lavoro, nell'ordine in cui vanno uniti."""
    names = [f"{track['id']}_init.mp4"] if track.get("init") else []
    return names + [f"{track['id']}_{index:05d}.ts" for index in range(len(track["segments"]))]


def tracks_from_signature(signature: list[dict]) -> list[dict]:
    """Ricostruisce dallo stato salvato le informazioni che servono a FFmpeg per unire le tracce."""
    return [{"id": t["id"], "kind": "video" if t["id"] == "video" else "audio", "label": t["label"],
             "language": t["language"], "segments": [None] * t["segments"], "init": t["init"] or None}
            for t in signature]


def segments_complete(work_dir: str, signature: list[dict] | None) -> bool:
    """True se tutti i segmenti delle tracce salvate sono già nella cartella di lavoro."""
    if not signature:
        return False
    return all(os.path.exists(os.path.join(work_dir, name))
               for track in tracks_from_signature(signature) for name in segment_files(track))


def mux_tracks(ffmpeg_path: str, work_dir: str, tracks: list[dict], output_file: str, log,
               progress=None, cancel_event: threading.Event | None = None, duration: float = 0.0):
    """Unisce con FFmpeg i segmenti di video e audio nel file MP4 finale, senza ricodifica.

    Il file viene creato nella cartella di lavoro e spostato al suo posto solo quando è completo:
    un'unione interrotta non lascia un MP4 a metà (illeggibile) con il nome definitivo.
    `progress(frazione)` riceve l'avanzamento; se `cancel_event` scatta FFmpeg viene fermato."""
    log(tr("log_merge_start"))
    use_concatf = ffmpeg_supports_concatf(ffmpeg_path)
    total_files = sum(len(segment_files(track)) for track in tracks)
    if not use_concatf:
        log(tr("log_no_concatf"))
    elif total_files > CONCATF_MAX_FILES:
        # «concatf» apre tutti i pezzi insieme: con i film lunghi si supera il limite di file aperti di
        # Windows («Too many open files»). Si incollano prima i pezzi di ogni traccia in un unico file.
        use_concatf = False
        log(tr("log_many_segments", n=total_files))
    temp_output = os.path.join(work_dir, "unione_in_corso.mp4")
    # -nostdin: FFmpeg non legge dal terminale (da cui potrebbe ricevere tasti o restare in attesa)
    cmd = [ffmpeg_path, "-hide_banner", "-nostdin", "-y", "-loglevel", "error", "-progress", "pipe:1", "-nostats"]
    joined_files = []
    process = None
    keep_temp = False  # Video già unito ma non spostabile al suo posto: non va cancellato
    errors: deque = deque(maxlen=40)
    try:
        for track in tracks:
            names = segment_files(track)
            if use_concatf:
                list_name = f"{track['id']}_elenco.txt"
                Path(work_dir, list_name).write_text("\n".join(names) + "\n", encoding="utf-8")
                cmd += ["-i", f"concatf:{list_name}"]  # Concatenazione dei segmenti come un unico flusso
            else:
                joined = f"{track['id']}_completo" + (".mp4" if track.get("init") else ".ts")
                joined_files.append(os.path.join(work_dir, joined))
                with open(joined_files[-1], "wb") as out:
                    for name in names:
                        if cancel_event and cancel_event.is_set():
                            raise DownloadCancelled()
                        with open(os.path.join(work_dir, name), "rb") as part:
                            shutil.copyfileobj(part, out, 1024 * 1024)
                cmd += ["-i", joined]

        audio_tracks = [t for t in tracks if t["kind"] == "audio"]
        if audio_tracks:
            cmd += ["-map", "0:v"]
            for n, track in enumerate(audio_tracks, start=1):
                cmd += ["-map", f"{n}:a"]
                language = iso639_2(track["language"]) if track["language"] else "und"
                cmd += [f"-metadata:s:a:{n - 1}", f"language={language}"]
                if track["label"]:
                    cmd += [f"-metadata:s:a:{n - 1}", f"title={track['label']}"]
                cmd += [f"-disposition:a:{n - 1}", "default" if n == 1 else "0"]
        else:
            cmd += ["-map", "0:v?", "-map", "0:a?"]
        # Niente «-movflags +faststart»: serve solo allo streaming web e costringe FFmpeg a riscrivere
        # l'intero file una seconda volta, raddoppiando la durata dell'unione.
        cmd += ["-c", "copy", temp_output]

        process = subprocess.Popen(cmd, cwd=work_dir, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="replace",
                                   creationflags=NO_WINDOW)
        threading.Thread(target=errors.extend, args=(process.stderr,), daemon=True).start()
        if cancel_event:
            def stop_on_cancel():
                while process.poll() is None:
                    if cancel_event.wait(0.3):
                        process.kill()
                        return
            threading.Thread(target=stop_on_cancel, daemon=True).start()

        for line in process.stdout:  # Righe «chiave=valore» di -progress, circa due al secondo
            key, _, value = line.strip().partition("=")
            if key == "out_time_us" and value.isdigit() and progress and duration:
                progress(min(int(value) / 1_000_000 / duration, 1.0))
        process.wait()

        if cancel_event and cancel_event.is_set():
            raise DownloadCancelled()
        if process.returncode != 0:
            details = "".join(errors).strip()[-1500:] or tr("err_ffmpeg_code", code=process.returncode)
            raise RuntimeError(tr("err_merge_failed", details=details))
        try:
            os.replace(temp_output, output_file)
        except OSError as err:
            keep_temp = True
            raise RuntimeError(tr("err_move_failed", path=output_file, err=err, temp=temp_output)) from err
    finally:
        if process is not None and process.poll() is None:
            process.kill()  # Mai lasciare FFmpeg al lavoro in background
            process.wait()
        for path in joined_files:
            remove_quietly(path)
        if not keep_temp:
            remove_quietly(temp_output)
    log(tr("log_done", path=output_file))


# ============================================================
# INTERFACCIA GRAFICA
# ============================================================
class StepIndicator:
    """Indicatore delle fasi (VPN → Browser → Download → File MP4) con cerchi numerati."""

    SYMBOLS = {"done": "✔", "warn": "!", "error": "✕"}

    def __init__(self, parent, names, font, caption_font):
        self.frame = ctk.CTkFrame(parent, fg_color="transparent")
        self.circles, self.captions, self.lines, self.states = [], [], [], []
        self._pulse_on = False
        for i, name in enumerate(names):
            circle = ctk.CTkLabel(self.frame, text=str(i + 1), width=32, height=32, corner_radius=16, font=font)
            circle.grid(row=0, column=i * 2)
            caption = ctk.CTkLabel(self.frame, text=name, font=caption_font, height=18)
            caption.grid(row=1, column=i * 2, pady=(4, 0))
            self.circles.append(circle)
            self.captions.append(caption)
            self.states.append("pending")
            if i < len(names) - 1:
                line = ctk.CTkFrame(self.frame, height=3, corner_radius=1, fg_color=CARD_BORDER)
                line.grid(row=0, column=i * 2 + 1, sticky="ew", padx=8)
                self.frame.grid_columnconfigure(i * 2 + 1, weight=1)
                self.lines.append(line)
        self.reset()

    def set_names(self, names):
        for caption, name in zip(self.captions, names):
            caption.configure(text=name)

    def reset(self):
        for i in range(len(self.circles)):
            self.set(i, "pending")

    def set(self, index: int, state: str):
        self.states[index] = state
        circle_color, text_color = STEP_STYLES[state]
        self.circles[index].configure(fg_color=circle_color, text_color=text_color,
                                      text=self.SYMBOLS.get(state, str(index + 1)))
        self.captions[index].configure(text_color=MUTED if state == "pending" else TEXT)
        if index < len(self.lines):
            line_color = {"done": SUCCESS_DARK, "warn": WARNING_DARK}.get(state, CARD_BORDER)
            self.lines[index].configure(fg_color=line_color)

    def pulse(self):
        """Fa «pulsare» il cerchio della fase in corso."""
        self._pulse_on = not self._pulse_on
        for circle, state in zip(self.circles, self.states):
            if state == "active":
                circle.configure(fg_color=ACCENT_LIGHT if self._pulse_on else ACCENT)


def _shorten(text: str, limit: int) -> str:
    return text if len(text) <= limit else text[:limit - 1] + "…"


def _display_path(path: str) -> str:
    """Percorso da mostrare con la cartella utente abbreviata in «~»: il nome utente non compare a schermo."""
    home = str(Path.home())
    return "~" + path[len(home):] if path.lower().startswith(home.lower()) else path


def _shorten_middle(text: str, limit: int) -> str:
    """Accorcia togliendo la parte centrale, così di un percorso restano inizio e nome finale."""
    if len(text) <= limit:
        return text
    keep = limit - 1
    return text[:keep // 2] + "…" + text[-(keep - keep // 2):]


class DownloaderApp:
    """Finestra principale: raccoglie i dati, gestisce la coda dei download, esegue i controlli e scarica."""

    def __init__(self, root: ctk.CTk):
        self.root = root
        self.events: queue.Queue = queue.Queue()  # Messaggi dai thread di lavoro alla GUI
        self.cancel_event = threading.Event()
        self.worker: threading.Thread | None = None
        self.busy = False  # Una coda di download è in lavorazione
        self.queue: list[dict] = []  # Download in attesa, nell'ordine in cui partiranno
        self.current_job: dict | None = None
        self.batch: list[tuple[dict, str, str]] = []  # (download, esito, dettagli) della coda in lavorazione
        self.last_output: str | None = None
        self.current_step: int | None = None
        self.samples: deque = deque()  # (secondi trascorsi, posizione video, byte) per velocità e ETA
        self.merge_started = 0.0
        self.settings = load_settings()

        # Stato dei testi variabili, per poterli riscrivere quando si cambia lingua
        self.translatable: list[tuple] = []  # (widget, chiave, opzione, argomenti)
        self.status_state: tuple = ("status_ready", "status_ready_sub", {})
        self.title_state: tuple | None = None
        self.tile_state: dict = {}
        self.job_label_state: tuple | None = None
        self.vpn_result: dict | None = None  # None = verifica in corso o non ancora fatta
        self.vpn_confirmed = False  # «Continua senza VPN» già confermato per la coda in corso
        self.panel = "queue"

        self.settings.pop("brave_path", None)  # Impostazione delle versioni precedenti
        self.browser = self._pick_browser()
        self.ffmpeg_path = find_ffmpeg()

        output_dir = self.settings.get("output_dir")
        if not output_dir or not os.path.isdir(output_dir):
            downloads = Path.home() / "Downloads"
            output_dir = str(downloads if downloads.is_dir() else Path.home())

        self._make_fonts()
        self._build_ui(output_dir)
        self._reset_progress_view()
        self._refresh_prerequisites()
        self._render_queue()
        self.start_vpn_check()

        missing = self._missing_libraries()
        if missing:
            self.root.after(400, lambda: messagebox.showwarning(
                tr("dlg_missing_libs_title"),
                tr("dlg_missing_libs_body", libs=", ".join(missing), cmd=" ".join(missing)),
                parent=self.root,
            ))
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(100, self._process_events)
        self.root.after(550, self._animate)

    # ---------------- Costruzione della finestra ----------------
    def _make_fonts(self):
        def font(size, weight="normal", family=FONT):
            return ctk.CTkFont(family=family, size=size, weight=weight)

        self.f_logo = font(22, "bold")
        self.f_title = font(24, "bold")
        self.f_caption = font(11, "bold")
        self.f_label = font(14, "bold")
        self.f_body = font(13)
        self.f_small = font(12)
        self.f_pill = font(12, "bold")
        self.f_step = font(13, "bold")
        self.f_percent = font(40, "bold")
        self.f_tile = font(16, "bold")
        self.f_button_big = font(16, "bold")
        self.f_log = font(11, family=MONO)

    def _tr(self, widget, key: str, option: str = "text", **kwargs):
        """Imposta un testo tradotto e lo ricorda per aggiornarlo al cambio di lingua."""
        self.translatable.append((widget, key, option, kwargs))
        widget.configure(**{option: tr(key, **kwargs)})
        return widget

    def _build_ui(self, output_dir: str):
        root = self.root
        root.title(APP_TITLE)
        # Finestra centrata e mai più alta dello schermo (lasciando spazio alla barra delle applicazioni)
        width = min(1100, root.winfo_screenwidth() - 40)
        height = min(800, root.winfo_screenheight() - 90)
        x = max((root.winfo_screenwidth() - width) // 2, 0)
        y = max((root.winfo_screenheight() - 50 - height) // 2, 0)
        root.geometry(f"{width}x{height}+{x}+{y}")
        root.minsize(min(1000, width), min(760, height))
        root.configure(fg_color=BG)

        main = ctk.CTkFrame(root, fg_color="transparent")
        main.pack(fill="both", expand=True, padx=24, pady=20)
        main.grid_columnconfigure((0, 1), weight=1, uniform="column")
        main.grid_rowconfigure(1, weight=1)

        self._build_header(main).grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 18))

        left = ctk.CTkFrame(main, fg_color="transparent")
        left.grid(row=1, column=0, sticky="nsew", padx=(0, 10))
        left.grid_columnconfigure(0, weight=1)
        self._build_video_card(left, output_dir).grid(row=0, column=0, sticky="ew")
        self._build_checks_card(left).grid(row=1, column=0, sticky="ew", pady=(16, 0))

        right = ctk.CTkFrame(main, fg_color="transparent")
        right.grid(row=1, column=1, sticky="nsew", padx=(10, 0))
        right.grid_columnconfigure(0, weight=1)
        right.grid_rowconfigure(1, weight=1)
        self._build_progress_card(right).grid(row=0, column=0, sticky="ew")
        self._build_panel_card(right).grid(row=1, column=0, sticky="nsew", pady=(16, 0))

        root.bind("<Return>", lambda _event: self.on_main_button())
        self.url_entry.focus_set()

    def _build_header(self, parent):
        header = ctk.CTkFrame(parent, fg_color="transparent")
        header.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(header, text="⬇", width=48, height=48, corner_radius=14, fg_color=ACCENT,
                     text_color="#ffffff", font=self.f_logo).grid(row=0, column=0, rowspan=2, padx=(0, 14))
        ctk.CTkLabel(header, text=APP_TITLE, font=self.f_title, text_color=TEXT, height=30,
                     anchor="w").grid(row=0, column=1, sticky="sw")
        self._tr(ctk.CTkLabel(header, font=self.f_small, text_color=MUTED, height=18, anchor="w"),
                 "header_subtitle").grid(row=1, column=1, sticky="nw")

        # Riquadro della lingua dell'app
        box = ctk.CTkFrame(header, fg_color=CARD, corner_radius=12, border_width=1, border_color=CARD_BORDER)
        box.grid(row=0, column=2, rowspan=2, sticky="e")
        self._tr(ctk.CTkLabel(box, font=self.f_small, text_color=MUTED, height=20),
                 "language_label").grid(row=0, column=0, padx=(14, 8), pady=8)
        self.language_menu = ctk.CTkOptionMenu(
            box, values=list(LANGUAGES.values()), command=self._on_language_change, width=130, height=30,
            corner_radius=8, font=self.f_body, dropdown_font=self.f_body, fg_color=SURFACE,
            button_color=SURFACE_HOVER, button_hover_color=ACCENT, text_color=TEXT,
            dropdown_fg_color=CARD, dropdown_hover_color=SURFACE_HOVER, dropdown_text_color=TEXT)
        self.language_menu.set(LANGUAGES[current_language()])
        self.language_menu.grid(row=0, column=1, padx=(0, 8), pady=8)
        return header

    def _card(self, parent, title_key: str):
        """Riquadro arrotondato con titolo; restituisce (riquadro, area contenuti)."""
        card = ctk.CTkFrame(parent, fg_color=CARD, corner_radius=16, border_width=1, border_color=CARD_BORDER)
        card.grid_columnconfigure(0, weight=1)
        card.grid_rowconfigure(1, weight=1)
        self._tr(ctk.CTkLabel(card, font=self.f_caption, text_color=MUTED, height=16, anchor="w"),
                 title_key).grid(row=0, column=0, sticky="w", padx=20, pady=(16, 10))
        body = ctk.CTkFrame(card, fg_color="transparent")
        body.grid(row=1, column=0, sticky="nsew", padx=20, pady=(0, 18))
        return card, body

    def _entry(self, parent, placeholder_key: str):
        entry = ctk.CTkEntry(parent, height=40, corner_radius=10, border_width=1, fg_color=INPUT,
                             border_color=CARD_BORDER, text_color=TEXT, placeholder_text_color=FAINT,
                             font=self.f_body)
        return self._tr(entry, placeholder_key, option="placeholder_text")

    def _secondary_button(self, parent, text_key: str, command, width: int = 100, height: int = 40, **kwargs):
        button = ctk.CTkButton(parent, command=command, width=width, height=height, corner_radius=10,
                               fg_color=SURFACE, hover_color=SURFACE_HOVER, border_width=1,
                               border_color=CARD_BORDER, text_color=TEXT, text_color_disabled=FAINT,
                               font=self.f_body)
        return self._tr(button, text_key, **kwargs)

    def _field_label(self, parent, key: str, row: int):
        self._tr(ctk.CTkLabel(parent, font=self.f_label, text_color=TEXT, height=20, anchor="w"), key).grid(
            row=row, column=0, columnspan=2, sticky="w", pady=(14 if row else 0, 6))

    def _build_video_card(self, parent, output_dir: str):
        card, body = self._card(parent, "card_video")
        body.grid_columnconfigure(0, weight=1)

        self._field_label(body, "field_url", 0)
        self.url_entry = self._entry(body, "placeholder_url")
        self.url_entry.grid(row=1, column=0, sticky="ew")
        self.paste_btn = self._secondary_button(body, "btn_paste", self.paste_url, width=110)
        self.paste_btn.grid(row=1, column=1, padx=(8, 0))

        self._field_label(body, "field_name", 2)
        self.name_entry = self._entry(body, "placeholder_name")
        self.name_entry.insert(0, tr("default_file_name"))
        self.name_entry.grid(row=3, column=0, sticky="ew")
        ctk.CTkLabel(body, text=".mp4", width=110, font=self.f_body, text_color=MUTED).grid(row=3, column=1, padx=(8, 0))

        self._field_label(body, "field_folder", 4)
        self.dir_entry = self._entry(body, "placeholder_folder")
        self.dir_entry.insert(0, output_dir)
        self.dir_entry.grid(row=5, column=0, sticky="ew")
        self.dir_btn = self._secondary_button(body, "btn_browse", self.choose_dir, width=110)
        self.dir_btn.grid(row=5, column=1, padx=(8, 0))

        self.download_btn = ctk.CTkButton(
            body, height=50, corner_radius=12, font=self.f_button_big, fg_color=ACCENT, hover_color=ACCENT_HOVER,
            text_color="#ffffff", text_color_disabled="#b9b0ff", command=self.on_main_button)
        self.download_btn.grid(row=6, column=0, columnspan=2, sticky="ew", pady=(22, 0))
        self._render_main_button()
        return card

    def _build_checks_card(self, parent):
        card, body = self._card(parent, "card_checks")
        body.grid_columnconfigure(1, weight=1)
        self.vpn_pill, self.vpn_detail = self._check_row(body, 0, "check_vpn")
        self.vpn_btn = self._secondary_button(body, "btn_recheck", self.start_vpn_check, width=130, height=30)
        self.vpn_btn.grid(row=0, column=2, sticky="e")
        self.browser_pill, self.browser_detail = self._check_row(body, 2, "check_browser")
        self.browser_btn = self._secondary_button(body, "btn_change", self.choose_browser, width=130, height=30)
        self.browser_btn.grid(row=2, column=2, sticky="e", pady=(12, 0))
        self.ffmpeg_pill, self.ffmpeg_detail = self._check_row(body, 4, "check_ffmpeg")

        self._tr(ctk.CTkLabel(body, font=self.f_label, text_color=TEXT, width=80, anchor="w"), "check_speed").grid(
            row=6, column=0, sticky="w", pady=(12, 0))
        self.workers_btn = ctk.CTkSegmentedButton(
            body, values=list(WORKER_CHOICES), command=self._on_workers_change, height=30, font=self.f_body,
            fg_color=SURFACE, selected_color=ACCENT, selected_hover_color=ACCENT_HOVER,
            unselected_color=SURFACE, unselected_hover_color=SURFACE_HOVER, text_color=TEXT)
        self.workers_btn.grid(row=6, column=1, sticky="w", pady=(12, 0))
        saved = str(self.settings.get("workers", SEGMENT_WORKERS))
        self.workers_btn.set(saved if saved in WORKER_CHOICES else str(SEGMENT_WORKERS))
        self._tr(ctk.CTkLabel(body, font=self.f_small, text_color=MUTED, height=16, anchor="w", justify="left",
                              wraplength=380), "speed_hint").grid(row=7, column=1, columnspan=2, sticky="w", pady=(4, 0))
        return card

    def _check_row(self, parent, row: int, name_key: str):
        top = 12 if row else 0
        self._tr(ctk.CTkLabel(parent, font=self.f_label, text_color=TEXT, width=80, anchor="w"), name_key).grid(
            row=row, column=0, sticky="w", pady=(top, 0))
        pill = ctk.CTkLabel(parent, text="", height=26, corner_radius=13, font=self.f_pill)
        pill.grid(row=row, column=1, sticky="w", pady=(top, 0))
        detail = ctk.CTkLabel(parent, text="", font=self.f_small, text_color=MUTED, height=16,
                              anchor="w", justify="left", wraplength=380)
        detail.grid(row=row + 1, column=1, columnspan=2, sticky="w", pady=(4, 0))
        return pill, detail

    def _build_progress_card(self, parent):
        card, body = self._card(parent, "card_download")
        body.grid_columnconfigure((0, 1), weight=1, uniform="tile")

        self.job_label = ctk.CTkLabel(body, text="", font=self.f_small, text_color=MUTED, height=18, anchor="w")
        self.job_label.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 10))

        self.steps = StepIndicator(body, self._step_names(), self.f_step, self.f_small)
        self.steps.frame.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(0, 18))

        head = ctk.CTkFrame(body, fg_color="transparent")
        head.grid(row=2, column=0, columnspan=2, sticky="ew")
        head.grid_columnconfigure(1, weight=1)
        self.percent_label = ctk.CTkLabel(head, text="—", width=120, height=52, font=self.f_percent,
                                          text_color=TEXT, anchor="w")
        self.percent_label.grid(row=0, column=0, rowspan=2, sticky="w", padx=(0, 10))
        self.status_label = ctk.CTkLabel(head, text="", font=self.f_label, text_color=TEXT, height=22, anchor="w")
        self.status_label.grid(row=0, column=1, sticky="sw")
        self.substatus_label = ctk.CTkLabel(head, text="", font=self.f_small, text_color=MUTED, height=18, anchor="w")
        self.substatus_label.grid(row=1, column=1, sticky="nw")

        self.progress_bar = ctk.CTkProgressBar(body, height=14, corner_radius=7, border_width=0,
                                               fg_color=SURFACE, progress_color=ACCENT)
        self.progress_bar.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(12, 16))

        self.tiles = {}
        tile_specs = (("size", "tile_size"), ("speed", "tile_speed"), ("eta", "tile_eta"), ("position", "tile_position"))
        for i, (key, caption_key) in enumerate(tile_specs):
            tile = ctk.CTkFrame(body, fg_color=TILE, corner_radius=12)
            tile.grid(row=4 + i // 2, column=i % 2, sticky="ew", padx=(0, 6) if i % 2 == 0 else (6, 0), pady=(0, 10))
            self._tr(ctk.CTkLabel(tile, font=self.f_small, text_color=MUTED, height=16, anchor="w"),
                     caption_key).pack(anchor="w", padx=14, pady=(10, 0))
            value = ctk.CTkLabel(tile, text="—", font=self.f_tile, text_color=TEXT, height=24, anchor="w")
            value.pack(anchor="w", padx=14, pady=(0, 10))
            self.tiles[key] = value

        buttons = ctk.CTkFrame(body, fg_color="transparent")
        buttons.grid(row=6, column=0, columnspan=2, sticky="ew", pady=(4, 0))
        buttons.grid_columnconfigure((0, 1), weight=1)
        self.cancel_btn = self._secondary_button(buttons, "btn_cancel", self.cancel_download, height=38)
        self.cancel_btn.grid(row=0, column=0, sticky="ew", padx=(0, 6))
        self.open_btn = self._secondary_button(buttons, "btn_open_folder", self.open_output_folder, height=38)
        self.open_btn.grid(row=0, column=1, sticky="ew", padx=(6, 0))
        self.cancel_btn.configure(state="disabled")
        self.open_btn.configure(state="disabled")
        return card

    def _build_panel_card(self, parent):
        """Riquadro in basso a destra con due schede: coda dei download e registro."""
        card = ctk.CTkFrame(parent, fg_color=CARD, corner_radius=16, border_width=1, border_color=CARD_BORDER)
        card.grid_columnconfigure(0, weight=1)
        card.grid_rowconfigure(1, weight=1)
        self.panel_switch = ctk.CTkSegmentedButton(
            card, values=["queue", "log"], command=self._on_panel_switch, height=30, font=self.f_body,
            fg_color=SURFACE, selected_color=ACCENT, selected_hover_color=ACCENT_HOVER,
            unselected_color=SURFACE, unselected_hover_color=SURFACE_HOVER, text_color=TEXT)
        self.panel_switch.grid(row=0, column=0, sticky="w", padx=20, pady=(14, 10))

        # Scheda «Coda»
        self.queue_frame = ctk.CTkFrame(card, fg_color="transparent")
        self.queue_frame.grid_columnconfigure(0, weight=1)
        self.queue_frame.grid_rowconfigure(0, weight=1)
        self.queue_list = ctk.CTkScrollableFrame(self.queue_frame, fg_color=INPUT, corner_radius=10, height=90,
                                                 scrollbar_button_color=SURFACE,
                                                 scrollbar_button_hover_color=SURFACE_HOVER)
        self.queue_list.grid(row=0, column=0, columnspan=2, sticky="nsew")
        self.queue_list.grid_columnconfigure(1, weight=1)
        self.start_queue_btn = self._secondary_button(self.queue_frame, "btn_start_queue", self.start_queue, height=32)
        self.start_queue_btn.grid(row=1, column=0, sticky="ew", pady=(10, 0), padx=(0, 6))
        self.clear_queue_btn = self._secondary_button(self.queue_frame, "btn_clear_queue", self.clear_queue, height=32)
        self.clear_queue_btn.grid(row=1, column=1, sticky="ew", pady=(10, 0), padx=(6, 0))
        self.queue_frame.grid_columnconfigure(1, weight=1)

        # Scheda «Registro»
        self.log_frame = ctk.CTkFrame(card, fg_color="transparent")
        self.log_frame.grid_rowconfigure(0, weight=1)
        self.log_frame.grid_columnconfigure(0, weight=1)
        self.log_box = ctk.CTkTextbox(self.log_frame, height=80, fg_color=INPUT, text_color="#a9b1c4",
                                      font=self.f_log, corner_radius=10, border_width=0, wrap="word",
                                      scrollbar_button_color=SURFACE, scrollbar_button_hover_color=SURFACE_HOVER)
        self.log_box.grid(row=0, column=0, sticky="nsew")
        self.log_box.configure(state="disabled")

        self._show_panel(self.panel)
        return card

    # ---------------- Lingua ----------------
    def _step_names(self) -> list[str]:
        return [tr("step_vpn"), tr("step_browser"), tr("step_download"), tr("step_mp4")]

    def _on_language_change(self, display_name: str):
        code = next((c for c, name in LANGUAGES.items() if name == display_name), "it")
        old_default = tr("default_file_name")
        set_language(code)
        if self.name_entry.get() == old_default:  # Nome predefinito non modificato: si traduce anche lui
            self.name_entry.delete(0, "end")
            self.name_entry.insert(0, tr("default_file_name"))
        self.language_menu.set(LANGUAGES[code])
        self.settings["language"] = code
        save_settings(self.settings)
        for widget, key, option, kwargs in self.translatable:
            widget.configure(**{option: tr(key, **kwargs)})
        self.steps.set_names(self._step_names())
        self._render_main_button()
        self._render_status()
        self._render_title()
        self._render_tiles()
        self._render_job_label()
        self._render_vpn()
        self._refresh_prerequisites()
        self._render_queue()

    # ---------------- Indicatori di stato ----------------
    def _set_check(self, pill, detail, state: str, label: str, info: str = ""):
        background, color = PILL_STYLES[state]
        pill.configure(text=f"●  {label}", fg_color=background, text_color=color)
        detail.configure(text=info)

    def _refresh_prerequisites(self):
        if self.browser and os.path.isfile(self.browser["path"]):
            note_key, note_args = self.browser["note"]
            self._set_check(self.browser_pill, self.browser_detail, "ok", self.browser["name"],
                            f"{tr(note_key, **note_args)} · {_shorten_middle(_display_path(self.browser['path']), 44)}")
        else:
            self._set_check(self.browser_pill, self.browser_detail, "error", tr("browser_none"),
                            tr("browser_none_detail"))
        self.browser_btn.configure(text=tr("btn_use_default") if self.settings.get("browser_path") else tr("btn_change"))
        if self.ffmpeg_path:
            self._set_check(self.ffmpeg_pill, self.ffmpeg_detail, "ok", tr("ffmpeg_found"),
                            _shorten_middle(_display_path(self.ffmpeg_path), 60))
        else:
            self._set_check(self.ffmpeg_pill, self.ffmpeg_detail, "error", tr("ffmpeg_missing"),
                            tr("ffmpeg_missing_detail"))

    def _render_vpn(self):
        if self.vpn_result is None:
            self._set_check(self.vpn_pill, self.vpn_detail, "pending", tr("vpn_checking"), tr("vpn_checking_detail"))
        elif self.vpn_result["active"]:
            self._set_check(self.vpn_pill, self.vpn_detail, "ok", tr("vpn_active"), describe_vpn(self.vpn_result))
        else:
            self._set_check(self.vpn_pill, self.vpn_detail, "warn", tr("vpn_inactive"), describe_vpn(self.vpn_result))

    def _set_status(self, title_key: str, sub_key: str | None = None, **kwargs):
        """Titolo e sottotitolo dello stato; gli argomenti possono essere funzioni (calcolate a ogni lingua)."""
        self.status_state = (title_key, sub_key, kwargs)
        self._render_status()

    def _render_status(self):
        title_key, sub_key, kwargs = self.status_state
        values = {k: (v() if callable(v) else v) for k, v in kwargs.items()}
        self.status_label.configure(text=tr(title_key, **values))
        self.substatus_label.configure(text=tr(sub_key, **values) if sub_key else "")

    def _set_title(self, key: str | None = None, **kwargs):
        self.title_state = (key, kwargs) if key else None
        self._render_title()

    def _render_title(self):
        if self.title_state:
            key, kwargs = self.title_state
            self.root.title(tr(key, app=APP_TITLE, **kwargs))
        else:
            self.root.title(APP_TITLE)

    def _set_tile(self, name: str, key: str = "raw", **kwargs):
        self.tile_state[name] = (key, kwargs)
        self._render_tiles(name)

    def _render_tiles(self, only: str | None = None):
        for name, (key, kwargs) in self.tile_state.items():
            if only is None or name == only:
                values = {k: (v() if callable(v) else v) for k, v in kwargs.items()}
                self.tiles[name].configure(text=tr(key, **values))

    def _render_job_label(self):
        if not self.job_label_state:
            self.job_label.configure(text="")
            return
        key, kwargs = self.job_label_state
        self.job_label.configure(text=tr(key, **kwargs))

    def _render_main_button(self):
        self.download_btn.configure(text=tr("btn_add_queue") if self.busy else tr("btn_download"))

    def _set_step(self, index: int, state: str = "active"):
        self.steps.set(index, state)
        if state == "active":
            self.current_step = index

    def _fail_current_step(self):
        if self.current_step is not None:
            self.steps.set(self.current_step, "error")
            self.current_step = None

    def _start_indeterminate(self):
        if self.progress_bar.cget("mode") != "indeterminate":
            self.progress_bar.configure(mode="indeterminate")
            self.progress_bar.start()

    def _stop_indeterminate(self):
        if self.progress_bar.cget("mode") == "indeterminate":
            self.progress_bar.stop()
            self.progress_bar.configure(mode="determinate")
            self.progress_bar.set(0)

    def _reset_progress_view(self):
        self.samples.clear()
        self.current_step = None
        self.steps.reset()
        self._stop_indeterminate()
        self.progress_bar.configure(progress_color=ACCENT)
        self.progress_bar.set(0)
        self.percent_label.configure(text="—", text_color=TEXT)
        for name in self.tiles:
            self._set_tile(name, text="—")
        self._set_status("status_ready", "status_ready_sub")
        self._set_title()

    # ---------------- Coda ----------------
    def _on_panel_switch(self, value: str):
        self._show_panel("log" if value == tr("tab_log") else "queue")

    def _show_panel(self, panel: str):
        self.panel = panel
        values = [tr("tab_queue", n=len(self.queue)), tr("tab_log")]
        self.panel_switch.configure(values=values)
        self.panel_switch.set(values[1] if panel == "log" else values[0])
        visible, hidden = (self.log_frame, self.queue_frame) if panel == "log" else (self.queue_frame, self.log_frame)
        hidden.grid_forget()
        visible.grid(row=1, column=0, sticky="nsew", padx=20, pady=(0, 18))

    def _render_queue(self):
        for child in self.queue_list.winfo_children():
            child.destroy()
        if not self.queue:
            self._tr_once(ctk.CTkLabel(self.queue_list, font=self.f_small, text_color=FAINT, justify="left",
                                       anchor="w", wraplength=400), "queue_empty").grid(
                row=0, column=0, columnspan=5, sticky="w", padx=10, pady=10)
        for i, job in enumerate(self.queue):
            ctk.CTkLabel(self.queue_list, text=f"{i + 1}", width=26, height=26, corner_radius=13, fg_color=SURFACE,
                         text_color=TEXT, font=self.f_pill).grid(row=i * 2, column=0, rowspan=2, padx=(8, 10), pady=6)
            name = _shorten(os.path.basename(job["output_file"]), 38)
            ctk.CTkLabel(self.queue_list, text=name, font=self.f_label, text_color=TEXT, height=18,
                         anchor="w").grid(row=i * 2, column=1, sticky="ew", pady=(6, 0))
            detail = _shorten_middle(os.path.dirname(job["output_file"]), 38)
            if job["resume_requested"]:
                detail += " · " + tr("queue_resumes")
            ctk.CTkLabel(self.queue_list, text=detail, font=self.f_small, text_color=MUTED, height=16,
                         anchor="w").grid(row=i * 2 + 1, column=1, sticky="ew", pady=(0, 6))
            for col, (symbol, command, enabled) in enumerate((
                    ("▲", lambda n=i: self.move_job(n, -1), i > 0),
                    ("▼", lambda n=i: self.move_job(n, 1), i < len(self.queue) - 1),
                    ("✕", lambda n=i: self.remove_job(n), True)), start=2):
                ctk.CTkButton(self.queue_list, text=symbol, width=28, height=28, corner_radius=8, fg_color=SURFACE,
                              hover_color=DANGER_DARK if symbol == "✕" else SURFACE_HOVER, text_color=TEXT,
                              text_color_disabled=FAINT, font=self.f_small, command=command,
                              state="normal" if enabled else "disabled").grid(
                    row=i * 2, column=col, rowspan=2, padx=(0, 8 if col == 4 else 4))
        self.start_queue_btn.configure(state="normal" if self.queue and not self.busy else "disabled")
        self.clear_queue_btn.configure(state="normal" if self.queue else "disabled")
        self._show_panel(self.panel)

    def _tr_once(self, widget, key: str, **kwargs):
        """Come _tr, per i widget che vengono ricreati a ogni aggiornamento (non vanno ricordati)."""
        widget.configure(text=tr(key, **kwargs))
        return widget

    def move_job(self, index: int, offset: int):
        target = index + offset
        if 0 <= target < len(self.queue):
            self.queue[index], self.queue[target] = self.queue[target], self.queue[index]
            self._render_queue()

    def remove_job(self, index: int):
        if 0 <= index < len(self.queue):
            job = self.queue.pop(index)
            self.log(tr("log_queue_removed", name=os.path.basename(job["output_file"])))
            self._render_queue()

    def clear_queue(self):
        if self.queue and messagebox.askyesno(tr("dlg_clear_queue_title"),
                                              tr("dlg_clear_queue_body", n=len(self.queue)), parent=self.root):
            self.queue.clear()
            self.log(tr("log_queue_cleared"))
            self._render_queue()

    def start_queue(self):
        if self.queue and not self.busy:
            self.batch = []
            self._set_busy(True)
            self._start_next()

    # ---------------- Azioni dei pulsanti ----------------
    def paste_url(self):
        try:
            text = self.root.clipboard_get().strip()
        except tk.TclError:
            return
        self.url_entry.delete(0, "end")
        self.url_entry.insert(0, text)

    def choose_dir(self):
        path = filedialog.askdirectory(parent=self.root, title=tr("dlg_choose_folder"),
                                       initialdir=self.dir_entry.get() or str(Path.home()))
        if path:
            self.dir_entry.delete(0, "end")
            self.dir_entry.insert(0, os.path.normpath(path))

    def _pick_browser(self) -> dict | None:
        """Browser scelto a mano (se impostato) oppure quello predefinito del PC."""
        manual = self.settings.get("browser_path")
        if manual and os.path.isfile(manual):
            return {"name": browser_display_name(manual), "path": manual, "note": ("note_manual", {})}
        if manual:  # Il browser scelto a mano non c'è più: si torna a quello predefinito
            self.settings.pop("browser_path")
            save_settings(self.settings)
        return detect_browser()

    def choose_browser(self):
        if self.settings.get("browser_path"):  # Il pulsante è «Usa predefinito»: torna alla scelta automatica
            self.settings.pop("browser_path")
            save_settings(self.settings)
            self.browser = self._pick_browser()
            self._refresh_prerequisites()
            return

        filetypes = [(tr("filetype_browser"), "*.exe")] if sys.platform == "win32" else [(tr("filetype_all"), "*")]
        path = filedialog.askopenfilename(parent=self.root, title=tr("dlg_choose_browser"), filetypes=filetypes)
        if not path:
            return
        path = os.path.normpath(path)
        if not _identify_browser(path) and not messagebox.askyesno(
                tr("dlg_browser_unknown_title"), tr("dlg_browser_unknown_body", name=browser_display_name(path)),
                icon="warning", parent=self.root):
            return
        self.settings["browser_path"] = path
        save_settings(self.settings)
        self.browser = self._pick_browser()
        self._refresh_prerequisites()

    def _on_workers_change(self, value: str):
        self.settings["workers"] = int(value)
        save_settings(self.settings)

    def open_output_folder(self):
        target = self.last_output if self.last_output and os.path.isfile(self.last_output) else None
        folder = os.path.dirname(target) if target else self.dir_entry.get()
        try:
            if sys.platform == "win32":
                if target:
                    subprocess.Popen(["explorer", "/select,", os.path.normpath(target)])
                else:
                    os.startfile(folder)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", "-R", target] if target else ["open", folder])
            else:
                subprocess.Popen(["xdg-open", folder])
        except OSError as err:
            messagebox.showerror(tr("dlg_error_title"), tr("dlg_open_folder_error", err=err), parent=self.root)

    def start_vpn_check(self, job: dict | None = None):
        """Verifica la VPN in background; se `job` è indicato, al termine prosegue con il download."""
        self.vpn_result = None
        self._render_vpn()
        self.vpn_btn.configure(state="disabled")

        def worker():
            try:
                result = check_vpn()
            except Exception as err:
                result = {"active": False, "error": str(err), "adapter": None}
            self.events.put(("vpn", (result, job)))

        threading.Thread(target=worker, daemon=True).start()

    @staticmethod
    def _missing_libraries() -> list[str]:
        return [name for name, module in (("playwright", async_playwright), ("pycryptodome", AES)) if module is None]

    def _is_taken(self, output_file: str) -> bool:
        """True se lo stesso file è già in download o in coda."""
        key = os.path.normcase(os.path.abspath(output_file))
        jobs = self.queue + ([self.current_job] if self.current_job else [])
        return any(os.path.normcase(os.path.abspath(job["output_file"])) == key for job in jobs)

    def _job_from_form(self) -> dict | None:
        """Controlla i campi e crea un download (chiedendo subito ciò che serve, così la coda procede da sola)."""
        page_url = self.url_entry.get().strip()
        # Link incollato due volte («…/watchinghttps://…/watching»): si tiene solo il primo indirizzo
        links = re.findall(r"https?://.*?(?=https?://|$)", page_url, re.IGNORECASE)
        if len(links) > 1:
            page_url = links[0].strip()
            self.url_entry.delete(0, "end")
            self.url_entry.insert(0, page_url)
        if not re.match(r"^https?://\S+$", page_url, re.IGNORECASE):
            messagebox.showerror(tr("dlg_invalid_url_title"), tr("dlg_invalid_url_body"), parent=self.root)
            self.url_entry.focus_set()
            return None

        file_name = sanitize_file_name(self.name_entry.get())
        if not file_name:
            messagebox.showerror(tr("dlg_invalid_name_title"), tr("dlg_invalid_name_body"), parent=self.root)
            self.name_entry.focus_set()
            return None

        output_dir = self.dir_entry.get().strip()
        if not output_dir:
            messagebox.showerror(tr("dlg_missing_folder_title"), tr("dlg_missing_folder_body"), parent=self.root)
            return None
        if not os.path.isdir(output_dir):
            if not messagebox.askyesno(tr("dlg_folder_missing_title"), tr("dlg_folder_missing_body", folder=output_dir),
                                       parent=self.root):
                return None
            try:
                os.makedirs(output_dir, exist_ok=True)
            except OSError as err:
                messagebox.showerror(tr("dlg_error_title"), tr("dlg_create_folder_error", err=err), parent=self.root)
                return None

        output_file = os.path.join(output_dir, file_name + ".mp4")
        if self._is_taken(output_file):
            messagebox.showerror(tr("dlg_duplicate_title"), tr("dlg_duplicate_body", name=file_name + ".mp4"),
                                 parent=self.root)
            return None

        resume = load_resume_state(output_file)
        resume_requested = False
        if resume and same_page(resume.get("page_url", ""), page_url):
            answer = messagebox.askyesnocancel(
                tr("dlg_interrupted_title"),
                tr("dlg_resume_body", name=file_name + ".mp4", progress=describe_progress(resume)),
                parent=self.root)
            if answer is None:
                return None
            resume_requested = bool(answer)
            if not answer:
                discard_partial(output_file)
        elif resume:
            if not messagebox.askyesno(tr("dlg_interrupted_title"),
                                       tr("dlg_other_page_body", name=file_name + ".mp4"),
                                       icon="warning", parent=self.root):
                return None
            discard_partial(output_file)
        elif has_segments(output_file):  # Parti scaricate senza le informazioni per riprenderle
            if not messagebox.askyesno(tr("dlg_interrupted_title"),
                                       tr("dlg_orphan_body", name=file_name + ".mp4"),
                                       icon="warning", parent=self.root):
                return None
            discard_partial(output_file)
        else:
            discard_partial(output_file)  # Eventuali avanzi senza segmenti

        if os.path.exists(output_file) and not messagebox.askyesno(
                tr("dlg_exists_title"), tr("dlg_exists_body", name=file_name + ".mp4"),
                icon="warning", parent=self.root):
            return None

        self.name_entry.delete(0, "end")
        self.name_entry.insert(0, file_name)
        self.settings["output_dir"] = output_dir
        save_settings(self.settings)
        return {"page_url": page_url, "output_file": output_file, "resume_requested": resume_requested}

    def on_main_button(self):
        """«Scarica» quando non c'è nulla in corso, «Aggiungi alla coda» durante un download."""
        job = self._job_from_form()
        if job is None:
            return
        if self.busy:
            self.queue.append(job)
            self.log(tr("log_queue_added", name=os.path.basename(job["output_file"]), n=len(self.queue)))
            self.url_entry.delete(0, "end")  # Pronto per il prossimo link
            self._render_queue()
            if self.panel != "queue":
                self._show_panel("queue")
            return
        self.queue.insert(0, job)  # Parte subito, poi prosegue con l'eventuale coda in pausa
        self._render_queue()
        self.start_queue()

    def cancel_download(self):
        if self.worker is not None and self.worker.is_alive():
            self.cancel_event.set()
            self.cancel_btn.configure(state="disabled")
            self._set_status("status_cancelling", "status_cancelling_sub")
            self.log(tr("log_cancel_requested"))

    def on_close(self):
        if self.busy or self.queue:
            if not messagebox.askyesno(tr("dlg_close_title"), tr("dlg_close_body", n=len(self.queue)),
                                       icon="warning", default="no", parent=self.root):
                return
        if self.worker is not None and self.worker.is_alive():
            # Attende che il browser, i download e FFmpeg vengano chiusi e che la parte scaricata venga salvata
            self.cancel_event.set()
            self.root.configure(cursor="watch")
            self.root.update_idletasks()
            self.worker.join(timeout=15)
        self.root.destroy()

    # ---------------- Esecuzione della coda ----------------
    def _start_next(self):
        """Avvia il primo download della coda (prima controlla browser, FFmpeg e VPN)."""
        if not self.queue:
            self._end_batch()
            return
        missing = self._missing_libraries()
        self.browser = self._pick_browser()  # Il browser predefinito potrebbe essere cambiato
        self.ffmpeg_path = find_ffmpeg()  # Potrebbe essere stato installato nel frattempo
        self._refresh_prerequisites()
        problem = None
        if missing:
            problem = (tr("dlg_missing_libs_title"), tr("dlg_missing_libs_body", libs=", ".join(missing),
                                                         cmd=" ".join(missing)))
        elif not self.browser or not os.path.isfile(self.browser["path"]):
            problem = (tr("dlg_browser_missing_title"), tr("dlg_browser_missing_body"))
        elif not self.ffmpeg_path:
            problem = (tr("dlg_ffmpeg_missing_title"), tr("dlg_ffmpeg_missing_body"))
        if problem:
            self._end_batch(summary=False)
            messagebox.showerror(*problem, parent=self.root)
            return

        job = self.queue.pop(0)
        job.update({
            "browser_path": self.browser["path"],
            "browser_name": self.browser["name"],
            "ffmpeg_path": self.ffmpeg_path,
            "workers": int(self.workers_btn.get()),
            "resume": load_resume_state(job["output_file"]) if job["resume_requested"] else None,
        })
        self.current_job = job
        self._render_queue()
        self.log("─" * 60)
        self.log(tr("log_job_start", name=os.path.basename(job["output_file"]), folder=os.path.dirname(job["output_file"])))
        self._reset_progress_view()
        self.job_label_state = ("job_label", {"name": os.path.basename(job["output_file"]),
                                              "left": len(self.queue)}) if self.queue else \
            ("job_label_single", {"name": os.path.basename(job["output_file"])})
        self._render_job_label()
        self._set_step(0)
        self._set_status("status_vpn_check", "status_vpn_check_sub")
        self._start_indeterminate()
        self.start_vpn_check(job)

    def _launch_worker(self, job: dict):
        self.cancel_event.clear()
        self.cancel_btn.configure(state="normal")
        self._set_step(1)
        self._set_status("status_searching", "status_searching_sub", browser=job["browser_name"])
        self._start_indeterminate()
        self.worker = threading.Thread(target=self._run_download, args=(job,), daemon=True)
        self.worker.start()

    def _job_finished(self, outcome: str, details: str = ""):
        """Registra l'esito del download in corso e passa al successivo (salvo annullamento)."""
        job = self.current_job
        self.current_job = None
        if job:
            self.batch.append((job, outcome, details))
        self.cancel_btn.configure(state="disabled")
        if outcome == "cancelled":
            if job:  # «Annulla» mette in pausa: il video torna in cima alla coda e «Avvia coda» lo riprende
                job["resume_requested"] = has_segments(job["output_file"])
                self.queue.insert(0, job)
            self._end_batch(summary=False)
        elif self.queue:
            self.log(tr("log_next_in_queue", n=len(self.queue)))
            self.root.after(1500, self._start_next)  # Breve pausa per vedere l'esito
        else:
            self._end_batch()

    def _end_batch(self, summary: bool = True):
        results, self.batch = self.batch, []
        self.current_job = None
        self.vpn_confirmed = False
        self._set_busy(False)
        self._stop_indeterminate()
        self._render_queue()
        if self.queue:
            self.job_label_state = ("job_label_paused", {"n": len(self.queue)})
            self._render_job_label()
        if not summary or not results:
            return
        if len(results) == 1:  # Un solo download: messaggi come senza coda
            job, outcome, details = results[0]
            if outcome == "done":
                if messagebox.askyesno(tr("dlg_done_title"), tr("dlg_done_body", path=job["output_file"]),
                                       parent=self.root):
                    self.open_output_folder()
            elif outcome == "incomplete":
                messagebox.showwarning(tr("dlg_incomplete_title"), tr("dlg_incomplete_body", progress=details),
                                       parent=self.root)
            elif outcome == "error":
                messagebox.showerror(tr("dlg_error_title"), details, parent=self.root)
            return

        done = [job for job, outcome, _ in results if outcome == "done"]
        failed = [(job, outcome, details) for job, outcome, details in results if outcome != "done"]
        lines = [tr("dlg_batch_body", done=len(done), failed=len(failed))]
        for job, outcome, details in failed:
            reason = tr("batch_incomplete", progress=details) if outcome == "incomplete" else details.splitlines()[0]
            lines.append(f"• {os.path.basename(job['output_file'])}: {_shorten(reason, 120)}")
        if failed:
            lines.append("")
            lines.append(tr("dlg_batch_failed_hint"))
            messagebox.showwarning(tr("dlg_batch_title"), "\n".join(lines), parent=self.root)
        elif messagebox.askyesno(tr("dlg_batch_title"), "\n".join(lines) + "\n\n" + tr("dlg_open_folder_question"),
                                 parent=self.root):
            self.open_output_folder()

    def _run_download(self, job: dict):
        """Eseguito in un thread separato: intercetta il flusso e ne scarica i segmenti.

        Se il server smette di accettare il collegamento (403), riapre la pagina nel browser per
        ottenerne uno nuovo e scarica solo i segmenti mancanti; alla fine crea il file MP4.
        """
        def log(message):
            self.events.put(("log", message))

        output_file = job["output_file"]
        work_dir = work_dir_for(output_file)
        state = job["resume"] or {"page_url": job["page_url"], "position": 0.0, "duration": None}
        state_lock = threading.Lock()
        last_save = [0.0]

        def checkpoint(stats: dict | None = None, force: bool = False):
            """Aggiorna stato.json (al massimo ogni STATE_SAVE_INTERVAL secondi): anche se il programma
            si chiude all'improvviso, al riavvio i segmenti già scaricati vengono riconosciuti."""
            with state_lock:
                if stats and stats["position"] > state["position"]:
                    state["position"] = stats["position"]
                    state["duration"] = stats["duration"]
                now = time.monotonic()
                if force or now - last_save[0] >= STATE_SAVE_INTERVAL:
                    last_save[0] = now
                    save_resume_state(output_file, state)

        def progress(stats):
            self.events.put(("progress", stats))
            checkpoint(stats)

        failures = 0
        subtitles: list[dict] = []
        tracks: list[dict] = []
        try:
            # Download già completo (es. interrotto durante l'unione): non serve riaprire il sito
            ready = bool(job["resume"]) and segments_complete(work_dir, state.get("tracks"))
            if ready and "subtitles" not in state and glob.glob(os.path.join(glob.escape(work_dir), "sub*.srt")):
                ready = False  # Sottotitoli senza lingua salvata: si rilegge la pagina (i segmenti non si riscaricano)
            if ready:
                log(tr("log_all_segments_present"))
                tracks = tracks_from_signature(state["tracks"])
                subtitles = [{**sub, "path": os.path.join(work_dir, f"{sub['id']}.srt")}
                             for sub in state.get("subtitles", [])
                             if os.path.exists(os.path.join(work_dir, f"{sub['id']}.srt"))]
            while not ready:
                self.events.put(("phase", ("browser", state["position"] > 0)))
                data = asyncio.run(intercept_hls_stream(job["page_url"], job["browser_path"], job["browser_name"],
                                                        log, self.cancel_event))
                if self.cancel_event.is_set():
                    raise DownloadCancelled()
                if "m3u8_url" not in data:
                    raise RuntimeError(tr("err_no_m3u8", seconds=TIMEOUT_PLAYWRIGHT))

                self.events.put(("phase", ("download", (state["position"], state["duration"]))))
                headers = {name: value for name, value in data["headers"].items() if value}
                client = HttpClient(cookies=data.get("cookies"))
                downloader = SegmentDownloader(work_dir, client, headers, log, progress, self.cancel_event,
                                               job["workers"], prefetched=data.get("prefetched"))
                try:
                    previous = state.get("tracks")
                    tracks, subtitles = resolve_tracks(data["m3u8_url"], headers, client,
                                                       previous[0]["label"] if previous else "",
                                                       body=data.get("body"))
                    signature = track_signature(tracks)
                    if previous and previous != signature:
                        raise RuntimeError(tr("err_version_changed", before=describe_tracks(previous),
                                              now=describe_tracks(signature)))
                    if not previous:
                        state["tracks"] = signature
                        checkpoint(force=True)  # Da qui in poi il download è riprendibile
                    if state["position"]:
                        log(tr("log_resuming", progress=describe_progress(state), workers=job["workers"]))
                    else:
                        audio = ", ".join(t["label"] or t["language"] or t["id"] for t in tracks if t["kind"] == "audio")
                        log(tr("log_tracks", video=tracks[0]["label"] or "", audio=audio or tr("audio_in_video"),
                               segments=len(tracks[0]["segments"]), workers=job["workers"]))
                    complete = downloader.run(tracks)
                    if complete and subtitles:
                        subtitles = download_subtitles(client, headers, subtitles, work_dir, log, self.cancel_event)
                    if complete:
                        with state_lock:  # Serve per unire i file anche senza riaprire il sito
                            state["subtitles"] = [{key: sub[key] for key in ("id", "label", "language", "forced")}
                                                  for sub in subtitles]
                except TokenExpired as err:
                    if not downloader.expired:
                        log(tr("log_request_refused", err=err))
                    complete = False
                finally:
                    client.close()
                    checkpoint(downloader.last_stats, force=True)

                if self.cancel_event.is_set():
                    raise DownloadCancelled()
                if complete:
                    break
                failures = failures + 1 if downloader.new_segments == 0 else 0
                if failures >= MAX_RESUME_ATTEMPTS:
                    raise IncompleteDownload()
                log(tr("log_reopening", attempt=failures + 1, total=MAX_RESUME_ATTEMPTS))

            self.events.put(("phase", ("merge", None)))
            duration = state.get("duration") or sum(s["duration"] or 0 for s in tracks[0]["segments"] if s)
            mux_tracks(job["ffmpeg_path"], work_dir, tracks, output_file, log,
                       progress=lambda fraction: self.events.put(("merge_progress", fraction)),
                       cancel_event=self.cancel_event, duration=duration)
            save_subtitles(subtitles, output_file, log)
            self.events.put(("phase", ("cleanup", None)))
            discard_partial(output_file)
        except DownloadCancelled:
            kept = has_segments(output_file)
            if not kept:
                discard_partial(output_file)
            self.events.put(("cancelled", {**state, "kept": kept}))
        except IncompleteDownload:
            if not has_segments(output_file):
                discard_partial(output_file)
                self.events.put(("error", tr("err_refused_403")))
            else:
                self.events.put(("incomplete", state))
        except Exception as err:
            message = str(err) or type(err).__name__
            if has_segments(output_file):
                message += "\n\n" + tr("err_partial_kept")
            else:
                discard_partial(output_file)
            self.events.put(("error", message))
        else:
            self.events.put(("done", output_file))

    # ---------------- Gestione degli eventi dai thread ----------------
    def _process_events(self):
        try:
            while True:
                try:
                    kind, payload = self.events.get_nowait()
                except queue.Empty:
                    break
                self._handle_event(kind, payload)
        finally:
            self.root.after(100, self._process_events)

    def _animate(self):
        self.steps.pulse()
        self.root.after(550, self._animate)

    def _handle_event(self, kind: str, payload):
        if kind == "log":
            self.log(payload)
        elif kind == "vpn":
            self._on_vpn_result(*payload)
        elif kind == "phase":
            self._on_phase(*payload)
        elif kind == "progress":
            self._on_progress(payload)
        elif kind == "merge_progress":
            self._on_merge_progress(payload)
        elif kind == "done":
            self._on_done(payload)
        elif kind == "cancelled":
            self._fail_current_step()
            self._stop_indeterminate()
            self.log(tr("log_cancelled"))
            if payload.get("kept"):
                self._set_status("status_paused", "status_paused_sub", progress=lambda: describe_progress(payload))
            else:
                self.progress_bar.set(0)
                self._set_status("status_cancelled", "status_cancelled_sub")
            self._job_finished("cancelled")
        elif kind == "incomplete":
            self._fail_current_step()
            self._stop_indeterminate()
            self.progress_bar.configure(progress_color=WARNING_DARK)
            reached = describe_progress(payload)
            self._set_status("status_incomplete", "status_incomplete_sub", progress=lambda: describe_progress(payload))
            self.log(tr("log_incomplete", progress=reached))
            self._job_finished("incomplete", reached)
        elif kind == "error":
            self._fail_current_step()
            self._stop_indeterminate()
            self.progress_bar.configure(progress_color=DANGER)
            self.percent_label.configure(text_color=DANGER)
            self._set_status("status_error", "raw", text=payload.splitlines()[0][:80])
            self.log(tr("log_error", err=payload))
            self._job_finished("error", payload)

    def _on_vpn_result(self, result: dict, job: dict | None):
        self.vpn_result = result
        self._render_vpn()
        self.log(tr("log_vpn", state=tr("vpn_active") if result["active"] else tr("vpn_inactive"),
                    details=describe_vpn(result)))
        if not self.busy:
            self.vpn_btn.configure(state="normal")
        if job is None:
            return

        if not result["active"] and self.vpn_confirmed:
            # Già confermato all'inizio di questa coda: non la si blocca a ogni video in attesa di un clic
            self.log(tr("log_vpn_still_missing"))
        elif not result["active"] and messagebox.askyesno(
                tr("dlg_no_vpn_title"), tr("dlg_no_vpn_body", details=describe_vpn(result)),
                icon="warning", default="no", parent=self.root):
            self.vpn_confirmed = True
        elif not result["active"]:
            self.log(tr("log_not_started_vpn"))
            self._fail_current_step()
            self.queue.insert(0, job)  # Torna in coda: si riparte con «Avvia coda»
            self.current_job = None
            self._end_batch(summary=False)
            self._set_status("status_not_started", "status_not_started_sub")
            return
        self._set_step(0, "done" if result["active"] else "warn")
        self._launch_worker(job)

    def _on_phase(self, name: str, value):
        browser_name = self.current_job["browser_name"] if self.current_job else ""
        if name == "browser":
            resuming = value
            self.steps.set(2, "pending")
            self._set_step(1)
            if resuming:  # La barra resta al punto raggiunto
                self._set_status("status_reconnecting", "status_reconnecting_sub", browser=browser_name)
                self._set_tile("speed", text="—")
                self._set_tile("eta", "tile_paused")
            else:
                self._set_status("status_searching", "status_searching_sub", browser=browser_name)
                self._start_indeterminate()
        elif name == "download":
            position, duration = value
            self.samples.clear()  # La velocità si ricalcola da capo per ogni parte
            self._set_step(1, "done")
            self._set_step(2)
            self._stop_indeterminate()
            if position and duration:
                fraction = min(position / duration, 1.0)
                self.progress_bar.set(fraction)
                self.percent_label.configure(text=f"{fraction * 100:.0f}%")
                state = {"position": position, "duration": duration}
                self._set_status("status_downloading", "status_resumed_sub", progress=lambda: describe_progress(state))
            else:
                self.percent_label.configure(text="0%")
                self._set_status("status_downloading", "status_connecting_sub")
        elif name == "merge":  # «Annulla» resta attivo: ferma FFmpeg e conserva i segmenti
            self._stop_indeterminate()
            for step in (1, 2):
                self._set_step(step, "done")
            self._set_step(3)
            self.merge_started = time.monotonic()
            self.progress_bar.set(0)
            self.percent_label.configure(text="0%")
            self._set_tile("speed", text="—")
            self._set_tile("eta", "tile_calculating")
            self._set_status("status_merging", "status_merging_sub")
        elif name == "cleanup":
            self.cancel_btn.configure(state="disabled")
            self._set_tile("eta", "tile_almost_done")
            self._set_status("status_cleanup", "status_cleanup_sub")

    def _on_merge_progress(self, fraction: float):
        self.progress_bar.set(fraction)
        percent = f"{fraction * 100:.0f}%"
        self.percent_label.configure(text=percent)
        self._set_title("title_merge", percent=percent)
        elapsed = time.monotonic() - self.merge_started
        if 0.02 < fraction < 1 and elapsed > 2:
            remaining = elapsed * (1 - fraction) / fraction
            self._set_tile("eta", text=lambda: _fmt_duration(remaining))
            self._set_status("status_merging", "status_merging_percent", percent=percent)
        elif fraction >= 1:
            self._set_tile("eta", "tile_almost_done")
            self._set_status("status_merging", "status_merging_final")

    def _on_progress(self, stats: dict):
        position, duration, size, wall = stats["position"], stats["duration"], stats["bytes"], stats["wall"]

        # Velocità e tempo rimanente calcolati sugli ultimi RATE_WINDOW secondi
        self.samples.append((wall, position or 0.0, size or 0))
        while len(self.samples) > 2 and self.samples[0][0] < wall - RATE_WINDOW:
            self.samples.popleft()
        first_wall, first_position, first_size = self.samples[0]
        elapsed = wall - first_wall
        byte_rate = (self.samples[-1][2] - first_size) / elapsed if elapsed > 0.5 else None
        position_rate = (self.samples[-1][1] - first_position) / elapsed if elapsed > 0.5 else None

        fraction = min(position / duration, 1.0) if duration and position is not None else None
        if fraction is None:
            self._start_indeterminate()
            self.percent_label.configure(text="…")
        else:
            self._stop_indeterminate()
            self.progress_bar.set(fraction)
            percent = f"{fraction * 100:.0f}%"
            self.percent_label.configure(text=percent)
            self._set_title("title_percent", percent=percent)

        if size is None:
            self._set_tile("size", text="—")
        elif fraction and fraction > 0.03:
            self._set_tile("size", text=f"{_fmt_bytes(size)} / ~{_fmt_bytes(size / fraction)}")
        else:
            self._set_tile("size", text=_fmt_bytes(size))
        if byte_rate:
            self._set_tile("speed", text=f"{_fmt_bytes(byte_rate)}/s")
        else:
            self._set_tile("speed", "tile_calculating")
        if position is not None:
            self._set_tile("position", text=f"{_fmt_time(position)} / {_fmt_time(duration)}" if duration
                           else _fmt_time(position))

        if fraction is not None and position_rate and position_rate > 0 and wall > 3:
            remaining = max(duration - position, 0) / position_rate
            finish_at = datetime.now() + timedelta(seconds=remaining)
            self._set_tile("eta", text=lambda: _fmt_duration(remaining))
            self._set_status("status_downloading", "status_finish_at", time=f"{finish_at:%H:%M}")
        else:
            self._set_tile("eta", "tile_calculating")
            self._set_status("status_downloading", "status_calculating_sub")

    def _on_done(self, output_file: str):
        self._set_step(2, "done")
        self._set_step(3, "done")
        self._stop_indeterminate()
        self.progress_bar.configure(progress_color=SUCCESS)
        self.progress_bar.set(1)
        self.percent_label.configure(text="100%", text_color=SUCCESS)
        self._set_tile("eta", "tile_finished")
        self._set_status("status_done", "raw", text=os.path.basename(output_file))
        self._set_title("title_done")
        self.last_output = output_file
        self.open_btn.configure(state="normal")
        self._job_finished("done")

    # ---------------- Stato della finestra ----------------
    def _set_busy(self, busy: bool):
        """Durante la coda restano attivi i campi (per aggiungere altri download); si bloccano solo
        i controlli che cambierebbero il download in corso."""
        self.busy = busy
        state = "disabled" if busy else "normal"
        for widget in (self.browser_btn, self.vpn_btn):
            widget.configure(state=state)
        self._render_main_button()
        if busy:
            self.open_btn.configure(state="disabled")
        else:
            self.cancel_btn.configure(state="disabled")
            self.job_label_state = None
            self._render_job_label()
        self._render_queue()

    def log(self, message: str):
        self.log_box.configure(state="normal")
        self.log_box.insert("end", message + "\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")


# ============================================================
# INSTALLAZIONE AUTOMATICA DELLE LIBRERIE
# ============================================================
def missing_packages() -> list[str]:
    """Pacchetti pip delle librerie che non risultano installate."""
    import importlib
    import importlib.util
    importlib.invalidate_caches()
    return [package for module, package in REQUIRED_PACKAGES.items() if importlib.util.find_spec(module) is None]


def install_packages(packages: list[str]) -> tuple[bool, str]:
    """Installa i pacchetti con il pip dello stesso Python che esegue lo script.
    Restituisce (riuscito, output di pip)."""
    cmd = [sys.executable, "-m", "pip", "install", "--disable-pip-version-check", *packages]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, errors="replace", creationflags=NO_WINDOW)
        if result.returncode == 0:
            return True, (result.stdout + result.stderr).strip()
        # Es. Python installato per tutti gli utenti: riprova nella cartella dell'utente
        retry = subprocess.run(cmd + ["--user"], capture_output=True, text=True, errors="replace",
                               creationflags=NO_WINDOW)
    except OSError as err:
        return False, str(err)
    if retry.returncode == 0:
        return True, (retry.stdout + retry.stderr).strip()
    return False, (result.stdout + result.stderr).strip()  # L'errore del primo tentativo è il più utile


def release_tk():
    """Elimina subito, nel thread principale, le finestre Tk già chiuse.

    Se restassero in memoria, il garbage collector potrebbe eliminarle più tardi da un thread
    secondario (es. il controllo VPN) e Tcl chiuderebbe il programma con
    «Tcl_AsyncDelete: async handler deleted by the wrong thread»."""
    import gc
    gc.collect()


def ensure_dependencies():
    """All'avvio installa le librerie mancanti mostrando una piccola finestra di attesa.
    Se sono già tutte presenti non fa nulla."""
    missing = missing_packages()
    if not missing:
        return

    names = ", ".join(missing)
    if sys.stdout:
        print(tr("console_installing", names=names))
    outcome = {}
    worker = threading.Thread(target=lambda: outcome.update(result=install_packages(missing)), daemon=True)

    splash = tk.Tk()
    splash.title(APP_TITLE)
    splash.configure(bg=BG)
    splash.resizable(False, False)
    tk.Label(splash, text=tr("splash_title"), bg=BG, fg=TEXT,
             font=(FONT, 12, "bold")).pack(padx=28, pady=(22, 4))
    tk.Label(splash, text=tr("splash_body", names=names), bg=BG, fg=MUTED,
             font=(FONT, 10)).pack(padx=28)
    bar = ttk.Progressbar(splash, mode="indeterminate", length=320)
    bar.pack(padx=28, pady=(14, 24))
    bar.start(12)

    def wait_for_install():
        if worker.is_alive():
            splash.after(200, wait_for_install)
        else:
            bar.stop()  # Altrimenti l'animazione della barra scatta a finestra già chiusa
            splash.destroy()

    worker.start()
    splash.after(200, wait_for_install)
    splash.mainloop()
    splash = bar = None
    release_tk()

    _, output = outcome.get("result", (False, tr("install_interrupted")))
    still_missing = missing_packages()
    if still_missing:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror(
            tr("dlg_install_failed_title"),
            tr("dlg_install_failed_body", libs=", ".join(still_missing), cmd=" ".join(still_missing),
               output=output[-800:]))
        root.destroy()
        root = None
        release_tk()
    elif sys.stdout:
        print(tr("console_installed"))
    load_optional_modules()


def main():
    set_language(load_settings().get("language", "it"))
    ensure_dependencies()
    if ctk is None:
        return  # L'errore è già stato mostrato da ensure_dependencies
    ctk.set_appearance_mode("dark")
    root = ctk.CTk()
    DownloaderApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()

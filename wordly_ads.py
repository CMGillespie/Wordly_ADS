"""
PROJECT: Wordly ADS — Audio Description System
VERSION: 1.0a
DESCRIPTION: Combines Wordly real-time transcription (WSS) with AI video frame
             analysis to produce WCAG-compliant audio description entries,
             written alongside transcript utterances into a single Google Doc.
AUTHOR: Chris Gillespie / Claude (Anthropic)
DATE: 2026-05-15
BASED ON: wordly_sales_tool_v4_1.py
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
import threading
import time
import datetime
import os
import shutil
import json
import re
import webbrowser
import websocket
import base64
import cv2
import yt_dlp
from dotenv import load_dotenv
from google.auth.transport.requests import Request
from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
import google.generativeai as genai
from PIL import Image
import io

# --- 1. CONFIGURATION ---
load_dotenv()
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY")

SCOPES = ['https://www.googleapis.com/auth/documents', 'https://www.googleapis.com/auth/drive']
WORDLY_ATTEND_URL = "wss://endpoint.wordly.ai/attend"

FRAME_INTERVAL_SECONDS = 5      # Sample one frame every N seconds
DESCRIPTION_PREFIX = "👁 [VISUAL] "  # Prefix for visual description entries

# --- 2. PATH MANAGEMENT ---
SYSTEM_DIR = "system_files"
PROMPTS_FILE = "prompts.json"
SETTINGS_FILE = os.path.join(SYSTEM_DIR, "settings.json")
TOKEN_FILE = os.path.join(SYSTEM_DIR, "token.json")
CREDS_FILE = os.path.join(SYSTEM_DIR, "credentials.json")

DEFAULT_PROMPTS = {
    "Meeting Summary": "Summarize this meeting transcript into key decisions, action items, and discussion points:",
    "City Council": "Summarize this city council meeting. Note motions, votes, speakers, and outcomes:",
    "Sales Call": "Summarize this sales call. Note customer pain points, next steps, and follow-up actions:"
}


class WordlyADS:
    def __init__(self, root):
        self.root = root
        self.root.title("Wordly ADS — Audio Description System v1.0")
        self.root.geometry("660x760")

        self.is_recording = False
        self.transcript_text = ""
        self.doc_id = None
        self.creds = None
        self.prompts = {}
        self.ws = None
        self.last_speaker_id = None
        self.last_speaker_tag = None

        # Vision state
        self.vision_active = False
        self.last_frame_desc = ""
        self.youtube_url = None
        self.vision_thread = None

        self.setup_folders()
        self.root.protocol("WM_DELETE_WINDOW", self.confirm_exit)
        self.load_prompts()
        self.build_ui()
        self.load_settings()
        self.authenticate_google()
        self.configure_genai()

    # -----------------------------------------------------------------------
    # SETUP
    # -----------------------------------------------------------------------

    def setup_folders(self):
        if not os.path.exists(SYSTEM_DIR):
            os.makedirs(SYSTEM_DIR)
        to_migrate = {
            "settings.json": SETTINGS_FILE,
            "token.json": TOKEN_FILE,
            "credentials.json": CREDS_FILE
        }
        for old_name, new_path in to_migrate.items():
            if os.path.exists(old_name) and not os.path.exists(new_path):
                try:
                    shutil.move(old_name, new_path)
                except Exception:
                    pass

    def load_prompts(self):
        try:
            if os.path.exists(PROMPTS_FILE):
                with open(PROMPTS_FILE, 'r', encoding='utf-8') as f:
                    loaded = json.load(f)
                    if isinstance(loaded, dict) and loaded:
                        self.prompts = loaded
                        return
            self.prompts = DEFAULT_PROMPTS.copy()
            self.save_prompts()
        except json.JSONDecodeError as e:
            messagebox.showerror("Prompt File Error",
                f"Formatting error in prompts.json:\n{e}\n\nUsing defaults for this session.")
            self.prompts = DEFAULT_PROMPTS.copy()

    def save_prompts(self):
        with open(PROMPTS_FILE, 'w') as f:
            json.dump(self.prompts, f, indent=2)

    def load_settings(self):
        try:
            if os.path.exists(SETTINGS_FILE):
                with open(SETTINGS_FILE, 'r') as f:
                    s = json.load(f)
                    self.session_id_var.set(s.get("session_id", ""))
                    self.passcode_var.set(s.get("passcode", ""))
                    self.folder_var.set(s.get("folder_url", ""))
                    self.youtube_var.set(s.get("youtube_url", ""))
                    saved_preset = s.get("preset", "")
                    if saved_preset in self.preset_combo['values']:
                        self.preset_var.set(saved_preset)
        except Exception:
            pass

    def save_settings(self):
        settings = {
            "session_id": self.session_id_var.get(),
            "passcode": self.passcode_var.get(),
            "folder_url": self.folder_var.get(),
            "youtube_url": self.youtube_var.get(),
            "preset": self.preset_var.get()
        }
        try:
            with open(SETTINGS_FILE, 'w') as f:
                json.dump(settings, f)
        except Exception as e:
            self.log(f"Settings Error: {e}")

    # -----------------------------------------------------------------------
    # UI
    # -----------------------------------------------------------------------

    def build_ui(self):
        # --- Wordly Connection ---
        conn_frame = ttk.LabelFrame(self.root, text="1. Wordly Connection", padding=10)
        conn_frame.pack(fill="x", padx=10, pady=5)

        ttk.Label(conn_frame, text="Session ID (Req):").grid(row=0, column=0, sticky="w", pady=2)
        self.session_id_var = tk.StringVar()
        self.session_id_var.trace_add("write", self.smart_format_session_id)
        self.session_id_entry = ttk.Entry(conn_frame, textvariable=self.session_id_var, width=20)
        self.session_id_entry.grid(row=0, column=1, sticky="w", pady=2, padx=5)

        ttk.Label(conn_frame, text="Passcode (Opt):").grid(row=1, column=0, sticky="w", pady=2)
        self.passcode_var = tk.StringVar()
        self.passcode_entry = ttk.Entry(conn_frame, textvariable=self.passcode_var, width=20)
        self.passcode_entry.grid(row=1, column=1, sticky="w", pady=2, padx=5)

        # --- Video Source ---
        video_frame = ttk.LabelFrame(self.root, text="2. Video Source (for Audio Description)", padding=10)
        video_frame.pack(fill="x", padx=10, pady=5)

        self.vision_enabled_var = tk.BooleanVar(value=False)
        self.vision_check = ttk.Checkbutton(video_frame, text="Enable Audio Description (Vision)",
                                             variable=self.vision_enabled_var,
                                             command=self.toggle_vision_fields)
        self.vision_check.pack(anchor="w")

        ttk.Label(video_frame, text="YouTube URL:").pack(anchor="w")
        self.youtube_var = tk.StringVar()
        self.youtube_entry = ttk.Entry(video_frame, textvariable=self.youtube_var, width=60, state="disabled")
        self.youtube_entry.pack(fill="x", pady=(0, 2))
        ttk.Label(video_frame, text="Leave blank if capturing video locally (VB-Cable / screen capture)",
                  foreground="gray").pack(anchor="w")

        # --- Session Details ---
        details_frame = ttk.LabelFrame(self.root, text="3. Session Details", padding=10)
        details_frame.pack(fill="x", padx=10, pady=5)

        ttk.Label(details_frame, text="Document Name (Optional):").pack(anchor="w")
        self.session_name_var = tk.StringVar()
        self.name_entry = ttk.Entry(details_frame, textvariable=self.session_name_var, width=55)
        self.name_entry.pack(fill="x", pady=(0, 5))

        ttk.Label(details_frame, text="Google Drive Folder URL (Optional):").pack(anchor="w")
        self.folder_var = tk.StringVar()
        self.folder_entry = ttk.Entry(details_frame, textvariable=self.folder_var, width=55)
        self.folder_entry.pack(fill="x", pady=(0, 5))

        ttk.Label(details_frame, text="Summary Type:").pack(anchor="w")
        self.preset_var = tk.StringVar()
        self.preset_combo = ttk.Combobox(details_frame, textvariable=self.preset_var, state="readonly")
        self.preset_combo['values'] = list(self.prompts.keys())
        if self.prompts:
            self.preset_combo.current(0)
        self.preset_combo.pack(fill="x")

        # --- Controls ---
        controls_frame = ttk.Frame(self.root, padding=10)
        controls_frame.pack(fill="x", padx=10)

        self.btn_start = ttk.Button(controls_frame, text="▶ START Session", command=self.start_workflow)
        self.btn_start.pack(side="left", fill="x", expand=True, padx=5)
        self.btn_stop = ttk.Button(controls_frame, text="⏹ STOP & Summarize",
                                   command=self.stop_workflow, state="disabled")
        self.btn_stop.pack(side="left", fill="x", expand=True, padx=5)

        self.status_label = ttk.Label(self.root, text="Ready.", foreground="blue",
                                      font=("Arial", 10, "bold"))
        self.status_label.pack(pady=5)

        self.log_area = scrolledtext.ScrolledText(self.root, height=10, state='disabled',
                                                   font=("Consolas", 9))
        self.log_area.pack(fill="both", expand=True, padx=10, pady=5)

        footer_frame = ttk.Frame(self.root, padding=10)
        footer_frame.pack(fill="x", side="bottom")
        self.btn_exit = ttk.Button(footer_frame, text="Exit", command=self.confirm_exit)
        self.btn_exit.pack(side="right")
        ttk.Label(footer_frame, text="Wordly ADS v1.0a").pack(side="left")

    def toggle_vision_fields(self):
        state = "normal" if self.vision_enabled_var.get() else "disabled"
        self.youtube_entry.config(state=state)

    def log(self, message):
        self.log_area.config(state='normal')
        self.log_area.insert(tk.END, f"{datetime.datetime.now().strftime('%H:%M:%S')} - {message}\n")
        self.log_area.see(tk.END)
        self.log_area.config(state='disabled')

    def confirm_exit(self):
        if messagebox.askyesno("Exit", "Are you sure?"):
            self.save_settings()
            self.is_recording = False
            self.vision_active = False
            if self.ws:
                self.ws.close()
            self.root.destroy()

    # -----------------------------------------------------------------------
    # AUTH & GENAI
    # -----------------------------------------------------------------------

    def configure_genai(self):
        if GEMINI_API_KEY:
            genai.configure(api_key=GEMINI_API_KEY)
            self.log("Gemini AI configured.")
        else:
            self.log("WARNING: GEMINI_API_KEY not found in .env")

    def authenticate_google(self):
        try:
            if os.path.exists(TOKEN_FILE):
                self.creds = Credentials.from_authorized_user_file(TOKEN_FILE, SCOPES)
            if not self.creds or not self.creds.valid:
                if self.creds and self.creds.expired and self.creds.refresh_token:
                    self.creds.refresh(Request())
                else:
                    if not os.path.exists(CREDS_FILE):
                        self.log("CRITICAL: credentials.json missing in system_files/")
                        return
                    flow = InstalledAppFlow.from_client_secrets_file(CREDS_FILE, SCOPES)
                    self.creds = flow.run_local_server(port=0)
                with open(TOKEN_FILE, 'w') as token:
                    token.write(self.creds.to_json())
            self.log("Google Auth OK.")
        except Exception as e:
            self.log(f"Auth Error: {e}")

    # -----------------------------------------------------------------------
    # SESSION ID FORMATTING
    # -----------------------------------------------------------------------

    def smart_format_session_id(self, *args):
        raw = self.session_id_var.get()
        cleaned = re.sub(r'[^a-zA-Z0-9]', '', raw).upper()
        formatted = f"{cleaned[:4]}-{cleaned[4:8]}" if len(cleaned) >= 4 else cleaned
        if raw != formatted:
            self.session_id_var.set(formatted)
            self.session_id_entry.icursor(tk.END)

    # -----------------------------------------------------------------------
    # GOOGLE DOC
    # -----------------------------------------------------------------------

    def extract_folder_id(self, input_string):
        if not input_string:
            return None
        match = re.search(r'folders/([a-zA-Z0-9_-]+)', input_string)
        return match.group(1) if match else (
            input_string if len(input_string) > 15 and "/" not in input_string else None
        )

    def create_google_doc(self, sid):
        try:
            docs_service = build('docs', 'v1', credentials=self.creds)
            drive_service = build('drive', 'v3', credentials=self.creds)

            base_name = self.session_name_var.get().strip() or "Wordly ADS Transcript"
            doc_title = f"{base_name} ({datetime.date.today().strftime('%Y-%m-%d')})"
            folder_id = self.extract_folder_id(self.folder_var.get().strip())

            doc = docs_service.documents().create(body={'title': doc_title}).execute()
            self.doc_id = doc.get('documentId')
            self.log(f"Created Doc: {doc_title}")

            if folder_id:
                file = drive_service.files().get(fileId=self.doc_id, fields='parents').execute()
                drive_service.files().update(
                    fileId=self.doc_id,
                    addParents=folder_id,
                    removeParents=",".join(file.get('parents', []))
                ).execute()

            st = datetime.datetime.now().strftime('%I:%M %p')
            ads_note = " | Audio Description: ON" if self.vision_enabled_var.get() else ""
            header = (
                f"Document Name: {base_name}\n"
                f"Wordly Session ID: {sid}\n"
                f"Date: {datetime.date.today().strftime('%B %d, %Y')}\n"
                f"Time: {st} - {{{{END_TIME}}}}{ads_note}\n\n"
                f"--------------------------------------------------\n"
                f"{{{{SUMMARY_GOES_HERE}}}}\n"
            )
            docs_service.documents().batchUpdate(
                documentId=self.doc_id,
                body={'requests': [{'insertText': {'location': {'index': 1}, 'text': header}}]}
            ).execute()

            webbrowser.open(f"https://docs.google.com/document/d/{self.doc_id}/edit")
            return True
        except Exception as e:
            self.log(f"Doc Error: {e}")
            self.reset_ui()
            return False

    def get_doc_length(self):
        try:
            doc = build('docs', 'v1', credentials=self.creds).documents().get(
                documentId=self.doc_id).execute()
            return doc.get('body').get('content')[-1].get('endIndex') - 1
        except Exception:
            return 1

    def push_text_to_doc_live(self, header_part, text_part, is_visual=False):
        """Push a block to the doc. Visual descriptions get italic + color styling."""
        try:
            docs_service = build('docs', 'v1', credentials=self.creds)
            current_len = self.get_doc_length()
            full_addition = f"{header_part}{text_part}"
            requests = [{'insertText': {'endOfSegmentLocation': {}, 'text': full_addition}}]

            if header_part and not is_visual:
                requests.append({'updateTextStyle': {
                    'range': {'startIndex': current_len, 'endIndex': current_len + len(header_part)},
                    'textStyle': {'bold': True, 'underline': True},
                    'fields': 'bold,underline'
                }})

            if is_visual:
                # Visual descriptions: bold prefix, italic body, foreground color
                requests.append({'updateTextStyle': {
                    'range': {'startIndex': current_len, 'endIndex': current_len + len(full_addition)},
                    'textStyle': {
                        'bold': True,
                        'italic': True,
                        'foregroundColor': {
                            'color': {'rgbColor': {'red': 0.13, 'green': 0.44, 'blue': 0.74}}
                        }
                    },
                    'fields': 'bold,italic,foregroundColor'
                }})
            else:
                requests.append({'updateTextStyle': {
                    'range': {'startIndex': current_len + len(header_part),
                              'endIndex': current_len + len(full_addition)},
                    'textStyle': {'bold': False, 'underline': False},
                    'fields': 'bold,underline'
                }})

            docs_service.documents().batchUpdate(
                documentId=self.doc_id,
                body={'requests': requests}
            ).execute()
        except Exception:
            pass

    # -----------------------------------------------------------------------
    # WORDLY WSS TRANSCRIPTION
    # -----------------------------------------------------------------------

    def transcription_loop(self, session_id, passcode):
        def on_open(ws):
            connect_msg = {"type": "connect", "presentationCode": session_id, "languageCode": "en"}
            if passcode:
                connect_msg["accessKey"] = passcode
            ws.send(json.dumps(connect_msg))

        def on_message(ws, message):
            try:
                data = json.loads(message)
                if data.get("type") == "phrase" and data.get("isFinal"):
                    text = data.get("translatedText", "").strip()
                    sid_cur = data.get("speakerId")
                    stag_cur = data.get("speakerTag")
                    name = data.get("name", "Speaker")
                    if not text:
                        return

                    has_tag_in_text = text.startswith(">>")
                    id_changed = (sid_cur != self.last_speaker_id)
                    voice_changed = (stag_cur != self.last_speaker_tag)

                    if id_changed or has_tag_in_text:
                        header = f"\n\n{name}: >> " if not has_tag_in_text else "\n\n"
                        self.push_text_to_doc_live(header, text)
                        self.transcript_text += (header + text)
                        self.last_speaker_id = sid_cur
                        self.last_speaker_tag = stag_cur
                    elif voice_changed:
                        header = "\n\n>> "
                        self.push_text_to_doc_live(header, text)
                        self.transcript_text += (header + text)
                        self.last_speaker_tag = stag_cur
                    else:
                        header = "\n\n"
                        self.push_text_to_doc_live(header, text)
                        self.transcript_text += (header + text)

                elif data.get("type") == "status" and not data.get("success"):
                    self.root.after(0, lambda: self.handle_auth_failure(data))
            except Exception:
                pass

        self.ws = websocket.WebSocketApp(WORDLY_ATTEND_URL, on_open=on_open, on_message=on_message)
        if self.is_recording:
            self.ws.run_forever()

    # -----------------------------------------------------------------------
    # VISION / FRAME ANALYSIS
    # -----------------------------------------------------------------------

    def get_youtube_stream_url(self, youtube_url):
        """Use yt-dlp to resolve a streamable video URL from YouTube."""
        try:
            ydl_opts = {
                'format': 'best[height<=720]',
                'quiet': True,
                'no_warnings': True,
            }
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(youtube_url, download=False)
                return info.get('url')
        except Exception as e:
            self.log(f"yt-dlp Error: {e}")
            return None

    def frame_to_base64(self, frame):
        """Convert OpenCV frame to base64 PNG for Gemini."""
        rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        img = Image.fromarray(rgb)
        buf = io.BytesIO()
        img.save(buf, format='PNG')
        return base64.b64encode(buf.getvalue()).decode('utf-8')

    def describe_frame(self, frame):
        """Send frame to Gemini Flash vision. Returns description string or None."""
        try:
            model = genai.GenerativeModel('gemini-1.5-flash')
            img_data = self.frame_to_base64(frame)

            prompt = (
                "You are generating audio descriptions for a blind or low-vision viewer watching "
                "a government meeting or public event. Describe only what has visually changed or "
                "is significant — on-screen text, slides, documents displayed, who is at the "
                "microphone, or notable actions. Be brief (1-2 sentences max). "
                "If there is nothing significant to describe, reply only with: NO_CHANGE"
            )

            response = model.generate_content([
                {'mime_type': 'image/png', 'data': img_data},
                prompt
            ])
            result = response.text.strip()
            if result == "NO_CHANGE" or not result:
                return None
            return result
        except Exception as e:
            self.log(f"Vision Error: {e}")
            return None

    def vision_loop(self, stream_url):
        """Continuous frame sampling and description loop."""
        self.log("Vision: Opening video stream...")
        cap = cv2.VideoCapture(stream_url)
        if not cap.isOpened():
            self.log("Vision: Could not open video stream.")
            return

        self.log(f"Vision: Stream open. Sampling every {FRAME_INTERVAL_SECONDS}s.")
        last_sample_time = 0

        while self.vision_active and self.is_recording:
            ret, frame = cap.read()
            if not ret:
                self.log("Vision: Stream ended or dropped.")
                break

            now = time.time()
            if now - last_sample_time >= FRAME_INTERVAL_SECONDS:
                last_sample_time = now
                description = self.describe_frame(frame)
                if description:
                    timestamp = datetime.datetime.now().strftime('%H:%M:%S')
                    entry = f"\n\n{DESCRIPTION_PREFIX}[{timestamp}] {description}"
                    self.push_text_to_doc_live("", entry, is_visual=True)
                    self.log(f"Visual: {description[:80]}...")
            else:
                time.sleep(0.1)

        cap.release()
        self.log("Vision: Stream closed.")

    # -----------------------------------------------------------------------
    # WORKFLOW
    # -----------------------------------------------------------------------

    def start_workflow(self):
        sid = self.session_id_var.get().strip()
        if not sid:
            messagebox.showwarning("Missing Session ID", "Please enter a Wordly Session ID.")
            return

        self.save_settings()
        self.is_recording = True
        self.transcript_text = ""
        self.last_speaker_id = None
        self.last_speaker_tag = None

        self.btn_start.config(state="disabled")
        self.btn_stop.config(state="normal")
        self.session_id_entry.config(state="disabled")
        self.passcode_entry.config(state="disabled")
        self.name_entry.config(state="disabled")
        self.folder_entry.config(state="disabled")
        self.preset_combo.config(state="disabled")
        self.vision_check.config(state="disabled")
        self.youtube_entry.config(state="disabled")

        self.status_label.config(text="● Recording & Transcribing...", foreground="red")

        if not self.create_google_doc(sid):
            return

        # Start Wordly WSS transcription
        threading.Thread(
            target=self.transcription_loop,
            args=(sid, self.passcode_var.get().strip()),
            daemon=True
        ).start()

        # Start vision loop if enabled
        if self.vision_enabled_var.get():
            youtube_url = self.youtube_var.get().strip()
            if youtube_url:
                self.log("Vision: Resolving YouTube stream URL...")
                def start_vision():
                    stream_url = self.get_youtube_stream_url(youtube_url)
                    if stream_url:
                        self.vision_active = True
                        self.vision_loop(stream_url)
                    else:
                        self.log("Vision: Could not resolve YouTube URL. Vision disabled.")
                self.vision_thread = threading.Thread(target=start_vision, daemon=True)
                self.vision_thread.start()
            else:
                self.log("Vision: No YouTube URL provided. Vision disabled for this session.")

    def handle_auth_failure(self, error_data=None):
        self.is_recording = False
        if self.ws:
            self.ws.close()
        msg = f"Wordly Error: {error_data.get('message', 'Unknown')}" if error_data else "Check Session ID"
        messagebox.showerror("Connection Error", msg)
        self.reset_ui()

    def stop_workflow(self):
        self.is_recording = False
        self.vision_active = False
        if self.ws:
            self.ws.close()
        self.status_label.config(text="Generating AI Summary...", foreground="orange")
        threading.Thread(target=self.finalize_meeting, daemon=True).start()

    def finalize_meeting(self):
        et = datetime.datetime.now().strftime('%I:%M %p')
        docs_service = build('docs', 'v1', credentials=self.creds)
        docs_service.documents().batchUpdate(
            documentId=self.doc_id,
            body={'requests': [{
                'replaceAllText': {
                    'containsText': {'text': '{{END_TIME}}', 'matchCase': True},
                    'replaceText': et
                }
            }]}
        ).execute()

        summary_raw = self.generate_summary()
        if summary_raw:
            title = f"--- AI SUMMARY ({self.preset_var.get()}) ---"
            clean_body = summary_raw.replace("**", "")
            full_text = f"{title}\n{clean_body}\n"

            docs_service.documents().batchUpdate(
                documentId=self.doc_id,
                body={'requests': [{
                    'replaceAllText': {
                        'containsText': {'text': '{{SUMMARY_GOES_HERE}}', 'matchCase': True},
                        'replaceText': full_text
                    }
                }]}
            ).execute()

            doc = docs_service.documents().get(documentId=self.doc_id).execute()
            start_offset = 1
            for element in doc['body']['content']:
                if 'paragraph' in element:
                    text = element['paragraph']['elements'][0].get('textRun', {}).get('content', '')
                    if title in text:
                        start_offset = element['startIndex']
                        break

            requests = [{'updateTextStyle': {
                'range': {'startIndex': start_offset, 'endIndex': start_offset + len(title)},
                'textStyle': {'bold': True, 'underline': True},
                'fields': 'bold,underline'
            }}]

            for match in re.finditer(r'\*\*(.*?)\*\*', summary_raw):
                header_text = match.group(1)
                found_idx = clean_body.find(header_text)
                if found_idx != -1:
                    header_start = start_offset + len(title) + 1 + found_idx
                    requests.append({'updateTextStyle': {
                        'range': {'startIndex': header_start,
                                  'endIndex': header_start + len(header_text)},
                        'textStyle': {'bold': True, 'underline': True},
                        'fields': 'bold,underline'
                    }})

            docs_service.documents().batchUpdate(
                documentId=self.doc_id,
                body={'requests': requests}
            ).execute()

        self.root.after(0, self.reset_ui)
        self.log("Session complete. Ready.")

    def generate_summary(self):
        try:
            model = genai.GenerativeModel('models/gemini-flash-latest')
            prompt = self.prompts.get(self.preset_var.get(), "Summarize:")
            return model.generate_content(f"{prompt}\n\nTRANSCRIPT:\n{self.transcript_text}").text
        except Exception as e:
            self.log(f"AI Summary Error: {e}")
            return None

    def reset_ui(self):
        self.status_label.config(text="Session saved. Ready for next session.", foreground="green")
        self.btn_start.config(state="normal")
        self.btn_stop.config(state="disabled")
        self.session_id_entry.config(state="normal")
        self.passcode_entry.config(state="normal")
        self.name_entry.config(state="normal")
        self.folder_entry.config(state="normal")
        self.preset_combo.config(state="readonly")
        self.vision_check.config(state="normal")
        self.toggle_vision_fields()


if __name__ == "__main__":
    root = tk.Tk()
    app = WordlyADS(root)
    root.mainloop()

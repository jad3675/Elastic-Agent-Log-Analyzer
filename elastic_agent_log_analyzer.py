#!/usr/bin/env python3
"""
Multi-Server Elastic Agent Log Analyzer - A GUI application for comparing and analyzing 
Elastic Agent logs across multiple servers
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import json
import re
from datetime import datetime, timezone, timedelta
from collections import defaultdict, Counter
import threading
from pathlib import Path
import statistics
import difflib

class ServerGroup:
    """Represents a group of log files from one server"""
    def __init__(self, name):
        self.name = name
        self.logs = []
        self.components = set()
        self.log_levels = set()
        self.loaded_files = set()
        
    def add_log(self, processed_log):
        self.logs.append(processed_log)
        self.components.add(processed_log['component'])
        self.log_levels.add(processed_log['level'])
        
    def clear(self):
        self.logs = []
        self.components = set()
        self.log_levels = set()
        self.loaded_files = set()
        
    def get_stats(self):
        return {
            'total_logs': len(self.logs),
            'components': len(self.components),
            'files': len(self.loaded_files),
            'errors': len([log for log in self.logs if log['level'].lower() == 'error']),
            'warnings': len([log for log in self.logs if log['level'].lower() in ['warn', 'warning']])
        }

class ComparisonEngine:
    """Handles comparison logic between server groups"""
    
    @staticmethod
    def calculate_similarity(str1, str2):
        """Calculate similarity ratio between two strings"""
        return difflib.SequenceMatcher(None, str1, str2).ratio()
    
    @staticmethod
    def find_similar_messages(logs1, logs2, similarity_threshold=0.7, time_window_minutes=5):
        """Find similar messages between two log sets within time windows"""
        correlations = []
        
        # Focus on errors and warnings for correlation
        important_logs1 = [log for log in logs1 if log['level'].lower() in ['error', 'warn', 'warning']]
        important_logs2 = [log for log in logs2 if log['level'].lower() in ['error', 'warn', 'warning']]
        
        for log1 in important_logs1:
            if log1['parsed_timestamp'] == datetime.min:
                continue
                
            for log2 in important_logs2:
                if log2['parsed_timestamp'] == datetime.min:
                    continue
                
                # Check time correlation (within time window)
                time_diff = abs((log1['parsed_timestamp'] - log2['parsed_timestamp']).total_seconds()) / 60
                if time_diff > time_window_minutes:
                    continue
                
                # Check message similarity
                similarity = ComparisonEngine.calculate_similarity(
                    log1['full_message'].lower(), 
                    log2['full_message'].lower()
                )
                
                if similarity >= similarity_threshold:
                    correlations.append({
                        'log1': log1,
                        'log2': log2,
                        'similarity': similarity,
                        'time_diff_minutes': time_diff,
                        'correlation_type': 'message_similarity'
                    })
        
        return sorted(correlations, key=lambda x: x['similarity'], reverse=True)
    
    @staticmethod
    def find_timeline_correlations(logs1, logs2, time_window_minutes=2):
        """Find timeline correlations - events happening at similar times"""
        correlations = []
        
        # Convert to int for range() function
        time_window_int = int(time_window_minutes)
        
        # Group logs by time buckets
        def get_time_bucket(timestamp, bucket_size_minutes=1):
            return timestamp.replace(second=0, microsecond=0) - timedelta(
                minutes=timestamp.minute % bucket_size_minutes
            )
        
        # Create time buckets for both servers
        buckets1 = defaultdict(list)
        buckets2 = defaultdict(list)
        
        for log in logs1:
            if log['parsed_timestamp'] != datetime.min:
                bucket = get_time_bucket(log['parsed_timestamp'])
                buckets1[bucket].append(log)
                
        for log in logs2:
            if log['parsed_timestamp'] != datetime.min:
                bucket = get_time_bucket(log['parsed_timestamp'])
                buckets2[bucket].append(log)
        
        # Find correlating time periods
        for bucket_time in buckets1.keys():
            # Check nearby time buckets - use int version for range()
            for minutes_offset in range(-time_window_int, time_window_int + 1):
                check_bucket = bucket_time + timedelta(minutes=minutes_offset)
                if check_bucket in buckets2:
                    bucket1_logs = buckets1[bucket_time]
                    bucket2_logs = buckets2[check_bucket]
                    
                    # Look for interesting correlations in this time period
                    bucket1_errors = [log for log in bucket1_logs if log['level'].lower() == 'error']
                    bucket2_errors = [log for log in bucket2_logs if log['level'].lower() == 'error']
                    
                    if bucket1_errors and bucket2_errors:
                        correlations.append({
                            'time_bucket': bucket_time,
                            'server1_events': len(bucket1_logs),
                            'server2_events': len(bucket2_logs),
                            'server1_errors': len(bucket1_errors),
                            'server2_errors': len(bucket2_errors),
                            'time_offset_minutes': minutes_offset,
                            'correlation_type': 'timeline_correlation'
                        })
        
        return correlations

class MultiServerLogViewer:
    def __init__(self, root):
        self.root = root
        self.root.title("Multi-Server Elastic Agent Log Analyzer")
        self.root.geometry("1400x900")
        
        # Data storage - now dynamic
        self.server_groups = {}
        self.server_display_names = {}
        self.server_viewers = {}
        self.server_frames = {}
        self.next_server_letter = 'A'  # Track next available letter
        
        self.comparison_results = []
        self.timezone_var = tk.StringVar(value="UTC")
        
        # Setup GUI containers and menus
        self.create_widgets()
        self.setup_layout()
        
        # Start with 2 default servers
        self.add_server_tab('A')
        self.add_server_tab('B')
        
        # Ensure UI reflects current servers
        self.update_menus()
        self.update_server_selection()
        self.update_status()
        
    def add_server_tab(self, letter=None):
        """Add a new server tab"""
        if letter is None:
            # Find next available letter
            letter = self.next_server_letter
            self.next_server_letter = chr(ord(self.next_server_letter) + 1)
        
        server_key = f'Server {letter}'
        display_name = server_key
        
        # Create server group and tracking
        self.server_groups[server_key] = ServerGroup(server_key)
        self.server_display_names[server_key] = display_name
        
        # Create tab frame
        server_frame = ttk.Frame(self.main_notebook)
        self.server_frames[server_key] = server_frame
        
        # Create server viewer
        server_viewer = ServerViewer(server_frame, server_key, self)
        self.server_viewers[server_key] = server_viewer
        
        # Add tab to notebook (insert before comparison tab)
        comparison_tab_index = self.main_notebook.index('end') - 1  # Comparison is last tab
        self.main_notebook.insert(comparison_tab_index, server_frame, text=display_name)
        
        # Update next letter for next time
        if letter == self.next_server_letter:
            if ord(self.next_server_letter) <= ord('Z'):
                self.next_server_letter = chr(ord(self.next_server_letter) + 1)
            else:
                # After Z, go to AA, AB, etc.
                if len(self.next_server_letter) == 1:
                    self.next_server_letter = 'AA'
                else:
                    # Increment the rightmost letter
                    letters = list(self.next_server_letter)
                    i = len(letters) - 1
                    while i >= 0:
                        if letters[i] < 'Z':
                            letters[i] = chr(ord(letters[i]) + 1)
                            break
                        letters[i] = 'A'
                        i -= 1
                    if i < 0:
                        letters = ['A'] + letters
                    self.next_server_letter = ''.join(letters)
        
        # Update selection checkboxes and menus/status
        self.update_server_selection()
        self.update_menus()
        self.update_status()
        return server_key
    
    def remove_server_tab(self, server_key):
        """Remove a server tab"""
        if len(self.server_groups) <= 1:
            messagebox.showwarning("Warning", "Cannot remove the last server tab")
            return
        
        if server_key in self.server_groups:
            # Find the tab index
            tab_index = None
            for i in range(self.main_notebook.index('end')):
                if self.main_notebook.tab(i, 'text') == self.server_display_names[server_key]:
                    tab_index = i
                    break
            
            if tab_index is not None:
                # Remove tab
                self.main_notebook.forget(tab_index)
                
                # Clean up data structures
                del self.server_groups[server_key]
                del self.server_display_names[server_key]
                del self.server_viewers[server_key]
                del self.server_frames[server_key]
                
                self.update_menus()
                self.update_server_selection()
                self.update_status()
                
                messagebox.showinfo("Success", f"Removed {server_key}")
    
    def update_menus(self):
        """Update dynamic menu items"""
        # Clear and rebuild the File menu with current servers
        self.rebuild_file_menu()
        self.rebuild_analysis_menu()
        self.rebuild_settings_menu()
        
    def rebuild_file_menu(self):
        """Rebuild File menu items dynamically"""
        if not hasattr(self, 'file_menu'):
            return
        self.file_menu.delete(0, 'end')
        
        # Load/Add per server
        for server_key in sorted(self.server_groups.keys()):
            display_name = self.server_display_names[server_key]
            self.file_menu.add_command(label=f"Load to {display_name}",
                                       command=lambda sk=server_key: self.load_file(sk))
            self.file_menu.add_command(label=f"Add to {display_name}",
                                       command=lambda sk=server_key: self.add_file(sk))
        
        self.file_menu.add_separator()
        
        # Clear per server + Clear All
        for server_key in sorted(self.server_groups.keys()):
            display_name = self.server_display_names[server_key]
            self.file_menu.add_command(label=f"Clear {display_name}",
                                       command=lambda sk=server_key: self.clear_server(sk))
        self.file_menu.add_command(label="Clear All", command=self.clear_all)
        
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Export Results", command=self.export_results)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Exit", command=self.root.quit)
        
    def rebuild_analysis_menu(self):
        """Rebuild Analysis menu with current servers"""
        if not hasattr(self, 'analysis_menu'):
            return
        self.analysis_menu.delete(0, 'end')
        
        for server_key in sorted(self.server_groups.keys()):
            display_name = self.server_display_names[server_key]
            self.analysis_menu.add_command(label=f"{display_name} Analysis",
                                           command=lambda sk=server_key: self.run_server_analysis(sk))
        
    def rebuild_settings_menu(self):
        """Rebuild Settings menu with current servers"""
        if not hasattr(self, 'settings_menu'):
            return
        self.settings_menu.delete(0, 'end')
        
        # Server management
        self.settings_menu.add_command(label="Add New Server", command=self.add_new_server)
        
        if len(self.server_groups) > 1:
            remove_menu = tk.Menu(self.settings_menu, tearoff=0)
            self.settings_menu.add_cascade(label="Remove Server", menu=remove_menu)
            for server_key in sorted(self.server_groups.keys()):
                display_name = self.server_display_names[server_key]
                remove_menu.add_command(label=display_name,
                                        command=lambda sk=server_key: self.remove_server_tab(sk))
        
        self.settings_menu.add_separator()
        
        # Rename commands
        rename_menu = tk.Menu(self.settings_menu, tearoff=0)
        self.settings_menu.add_cascade(label="Rename Server", menu=rename_menu)
        for server_key in sorted(self.server_groups.keys()):
            display_name = self.server_display_names[server_key]
            rename_menu.add_command(label=display_name,
                                    command=lambda sk=server_key: self.rename_server(sk))
        
        self.settings_menu.add_separator()
        self.settings_menu.add_command(label="Reset All Names", command=self.reset_server_names)
    
    def create_widgets(self):
        """Initialize menubar, main frame, notebook, and comparison tab"""
        # Menubar
        self.menubar = tk.Menu(self.root)
        self.root.config(menu=self.menubar)
        
        # File menu (dynamic items)
        self.file_menu = tk.Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label="File", menu=self.file_menu)
        
        # Compare menu (static actions)
        self.compare_menu = tk.Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label="Compare", menu=self.compare_menu)
        self.compare_menu.add_command(label="Run Full Comparison", command=self.run_comparison)
        self.compare_menu.add_command(label="Timeline Correlation", command=self.run_timeline_correlation)
        self.compare_menu.add_command(label="Message Similarity", command=self.run_message_similarity)
        self.compare_menu.add_command(label="Component Analysis", command=self.run_component_comparison)
        
        # Analysis menu (dynamic per-server actions)
        self.analysis_menu = tk.Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label="Analysis", menu=self.analysis_menu)
        
        # Settings menu (dynamic server management)
        self.settings_menu = tk.Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label="Settings", menu=self.settings_menu)
        
        # Main container
        self.main_frame = ttk.Frame(self.root)
        
        # Status bar
        self.status_var = tk.StringVar(value="Ready - Load log files to servers")
        self.status_bar = ttk.Label(self.main_frame, textvariable=self.status_var, relief=tk.SUNKEN)
        
        # Main notebook for tabs
        self.main_notebook = ttk.Notebook(self.main_frame)
        
        # Comparison tab
        self.comparison_frame = ttk.Frame(self.main_notebook)
        self.setup_comparison_tab()
        self.main_notebook.add(self.comparison_frame, text="Comparison")
        
        # Populate dynamic menus initially
        self.update_menus()
    def add_new_server(self):
        """Add a new server tab via menu command"""
        server_key = self.add_server_tab()
        messagebox.showinfo("Success", f"Added {server_key}")
        
        # Switch to the new tab
        if server_key in self.server_frames:
            self.main_notebook.select(self.server_frames[server_key])
        
        # Ensure server selection UI reflects the new tab
        self.update_server_selection()
        
    def setup_comparison_tab(self):
        # Comparison controls
        control_frame = ttk.Frame(self.comparison_frame)
        control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(control_frame, text="Run Full Comparison", command=self.run_comparison).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Timeline Analysis", command=self.run_timeline_correlation).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Message Similarity", command=self.run_message_similarity).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Export Results", command=self.export_results).pack(side=tk.LEFT, padx=5)
        
        # Server selection frame
        selection_frame = ttk.LabelFrame(control_frame, text="Select Servers to Compare")
        selection_frame.pack(side=tk.LEFT, padx=10)
        
        self.server_selection_vars = {}
        self.server_checkboxes = {}
        
        # Will be populated dynamically
        self.update_server_selection()
        
        # Settings frame
        settings_frame = ttk.LabelFrame(control_frame, text="Comparison Settings")
        settings_frame.pack(side=tk.RIGHT, padx=5)
        
        ttk.Label(settings_frame, text="Time Window (min):").pack(side=tk.LEFT)
        self.time_window_var = tk.StringVar(value="5")
        ttk.Entry(settings_frame, textvariable=self.time_window_var, width=5).pack(side=tk.LEFT, padx=2)
        
        ttk.Label(settings_frame, text="Similarity:").pack(side=tk.LEFT, padx=(10,0))
        self.similarity_var = tk.StringVar(value="0.7")
        ttk.Entry(settings_frame, textvariable=self.similarity_var, width=5).pack(side=tk.LEFT, padx=2)
        
        # Results display
        self.comparison_text = scrolledtext.ScrolledText(self.comparison_frame, wrap=tk.WORD, height=35)
        self.comparison_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
    def update_server_selection(self):
        """Update server selection checkboxes"""
        # Clear existing checkboxes
        for widget in self.server_checkboxes.values():
            widget.destroy()
        self.server_checkboxes.clear()
        self.server_selection_vars.clear()
        
        # Create new checkboxes for current servers
        selection_frame = None
        for widget in self.comparison_frame.winfo_children():
            if isinstance(widget, ttk.Frame):
                for child in widget.winfo_children():
                    if isinstance(child, ttk.LabelFrame) and 'Select Servers' in str(child['text']):
                        selection_frame = child
                        break
                if selection_frame:
                    break
        
        if selection_frame:
            row = 0
            col = 0
            for server_key in sorted(self.server_groups.keys()):
                display_name = self.server_display_names[server_key]
                var = tk.BooleanVar(value=True)  # Default to selected
                self.server_selection_vars[server_key] = var
                
                cb = ttk.Checkbutton(selection_frame, text=display_name, variable=var)
                cb.grid(row=row, column=col, sticky='w', padx=2, pady=1)
                self.server_checkboxes[server_key] = cb
                
                col += 1
                if col > 2:  # 3 columns max
                    col = 0
                    row += 1
                    
    def get_selected_servers(self):
        """Get list of selected servers for comparison"""
        selected = []
        for server_key, var in self.server_selection_vars.items():
            if var.get() and self.server_groups[server_key].logs:  # Only include servers with data
                selected.append(server_key)
        return selected
        
    def validate_comparison(self):
        """Validate that at least 2 servers are selected for comparison"""
        selected = self.get_selected_servers()
        if len(selected) < 2:
            messagebox.showwarning("Warning", "Please select at least 2 servers with data for comparison")
            return False
        return True
        
    def setup_layout(self):
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.main_notebook.pack(fill=tk.BOTH, expand=True, pady=(0, 5))
        self.status_bar.pack(fill=tk.X)
        
    # File operations
    def load_file(self, server_name):
        file_path = filedialog.askopenfilename(
            title=f"Load Log File to {server_name}",
            filetypes=[("All Files", "*.*"), ("Log Files", "*.log"), ("JSON Files", "*.json")]
        )
        
        if file_path:
            self.server_groups[server_name].clear()
            threading.Thread(target=self._load_file_thread, args=(file_path, server_name), daemon=True).start()
            
    def add_file(self, server_name):
        file_path = filedialog.askopenfilename(
            title=f"Add Log File to {server_name}",
            filetypes=[("All Files", "*.*"), ("Log Files", "*.log"), ("JSON Files", "*.json")]
        )
        
        if file_path:
            file_name = Path(file_path).name
            if file_name in self.server_groups[server_name].loaded_files:
                messagebox.showwarning("Warning", f"File '{file_name}' is already loaded to {server_name}")
                return
            threading.Thread(target=self._load_file_thread, args=(file_path, server_name), daemon=True).start()
            
        
    def _load_file_thread(self, file_path, server_name):
        try:
            file_name = Path(file_path).name
            self.status_var.set(f"Loading {file_name} to {server_name}...")
            
            server_group = self.server_groups[server_name]
            server_group.loaded_files.add(file_name)
            
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read().strip()
                
            lines = content.split('\n') if '\n' in content else [content]
            new_logs = []
            
            for line_num, line in enumerate(lines, 1):
                line = line.strip()
                if not line:
                    continue
                    
                try:
                    log_entry = json.loads(line)
                    processed_entry = self.process_log_entry(log_entry, line_num, file_name, server_name)
                    if processed_entry:
                        new_logs.append(processed_entry)
                        server_group.add_log(processed_entry)
                except json.JSONDecodeError as e:
                    print(f"Error parsing line {line_num} in {file_name}: {e}")
                    continue
            
            # Sort logs by timestamp
            server_group.logs.sort(key=lambda x: x.get('parsed_timestamp', datetime.min))
            
            # Update UI on main thread
            self.root.after(0, self._update_ui_after_load, server_name, file_path, len(new_logs))
            
        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("Error", f"Failed to load file: {str(e)}"))
            self.status_var.set("Error loading file")
            
    def process_log_entry(self, entry, line_num, file_name, server_name):
        """Process and normalize a log entry"""
        processed = {
            'raw': entry,
            'line_number': line_num,
            'file_name': file_name,
            'server_name': server_name
        }
        
        # Extract timestamp
        timestamp_str = entry.get('@timestamp', '')
        if timestamp_str:
            try:
                utc_timestamp = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))
                processed['parsed_timestamp'] = utc_timestamp
                
                # Convert to selected timezone for display
                local_timestamp = self.convert_timezone(utc_timestamp)
                tz_name = self.get_timezone_name()
                processed['timestamp'] = local_timestamp.strftime(f'%Y-%m-%d %H:%M:%S {tz_name}')
            except:
                processed['timestamp'] = timestamp_str
                processed['parsed_timestamp'] = datetime.min
        else:
            processed['timestamp'] = 'N/A'
            processed['parsed_timestamp'] = datetime.min
            
        # Extract log level
        log_level = entry.get('log.level', 'unknown')
        processed['level'] = log_level
        
        # Extract component
        component = 'unknown'
        if 'component' in entry:
            comp_info = entry['component']
            if isinstance(comp_info, dict):
                component = comp_info.get('binary', comp_info.get('type', 'unknown'))
            else:
                component = str(comp_info)
        elif 'service.name' in entry:
            component = entry['service.name']
            
        processed['component'] = component
        
        # Extract message
        message = entry.get('message', '')
        processed['message'] = message[:100] + '...' if len(message) > 100 else message
        processed['full_message'] = message
        
        return processed
        
    def _update_ui_after_load(self, server_name, file_path, new_log_count):
        """Update UI after file is loaded"""
        viewer = self.server_viewers.get(server_name)
        if viewer:
            viewer.refresh_display()
        self.update_status()
        
    def update_status(self):
        """Update status bar with all server stats"""
        if not self.server_groups:
            self.status_var.set("No servers loaded")
            return
            
        status_parts = []
        total_logs = 0
        servers_with_data = 0
        
        for server_key in sorted(self.server_groups.keys()):
            stats = self.server_groups[server_key].get_stats()
            display_name = self.server_display_names[server_key]
            
            if stats['total_logs'] > 0:
                servers_with_data += 1
                
            status_parts.append(f"{display_name}: {stats['total_logs']} logs ({stats['files']} files)")
            total_logs += stats['total_logs']
        
        status = " | ".join(status_parts)
        
        if servers_with_data >= 2:
            status += " | Ready for comparison"
        elif len(self.server_groups) > 1:
            status += " | Load data to multiple servers for comparison"
            
        self.status_var.set(status)
        
    def clear_all(self):
        """Clear all servers"""
        for server_key in list(self.server_groups.keys()):
            self.clear_server(server_key)
        self.comparison_text.delete(1.0, tk.END)
        
    def clear_server(self, server_key):
        """Clear a specific server"""
        if server_key in self.server_groups:
            self.server_groups[server_key].clear()
            if server_key in self.server_viewers:
                self.server_viewers[server_key].refresh_display()
            self.update_status()
        
    def on_timezone_change(self, event=None):
        """Handle timezone selection change for all servers"""
        # Reprocess all logs to update timestamps
        for server_key in self.server_groups:
            for log in self.server_groups[server_key].logs:
                if log['parsed_timestamp'] != datetime.min:
                    local_timestamp = self.convert_timezone(log['parsed_timestamp'])
                    tz_name = self.get_timezone_name()
                    log['timestamp'] = local_timestamp.strftime(f'%Y-%m-%d %H:%M:%S {tz_name}')
        
        # Update all displays
        for server_key in self.server_viewers:
            self.server_viewers[server_key].refresh_display()
            
    def rename_server(self, server_key):
        """Rename a server tab"""
        current_name = self.server_display_names[server_key]
        
        # Create a simple dialog for renaming
        dialog = tk.Toplevel(self.root)
        dialog.title(f"Rename {current_name}")
        dialog.geometry("300x120")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Center the dialog
        dialog.geometry(f"+{self.root.winfo_rootx() + 50}+{self.root.winfo_rooty() + 50}")
        
        tk.Label(dialog, text=f"Enter new name for {current_name}:").pack(pady=10)
        
        name_var = tk.StringVar(value=current_name)
        entry = tk.Entry(dialog, textvariable=name_var, width=30)
        entry.pack(pady=5)
        entry.select_range(0, tk.END)
        entry.focus()
        
        def apply_rename():
            new_name = name_var.get().strip()
            if new_name and new_name != current_name:
                self.server_display_names[server_key] = new_name
                
                # Update tab text for this server
                frame = self.server_frames.get(server_key)
                if frame is not None:
                    self.main_notebook.tab(frame, text=new_name)
                
                # Update server viewer display name
                viewer = self.server_viewers.get(server_key)
                if viewer:
                    viewer.update_server_name(new_name)
                
                # Refresh status
                self.update_status()
                
            dialog.destroy()
        
        def cancel_rename():
            dialog.destroy()
        
        button_frame = tk.Frame(dialog)
        button_frame.pack(pady=10)
        
        tk.Button(button_frame, text="OK", command=apply_rename, width=8).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Cancel", command=cancel_rename, width=8).pack(side=tk.LEFT, padx=5)
        
        # Bind Enter key to apply
        entry.bind('<Return>', lambda e: apply_rename())
        dialog.bind('<Escape>', lambda e: cancel_rename())
        
    def reset_server_names(self):
        """Reset all server names to defaults"""
        for server_key in self.server_groups.keys():
            self.server_display_names[server_key] = server_key
            
        # Update tab texts
        for i in range(self.main_notebook.index('end')):
            tab_text = self.main_notebook.tab(i, 'text')
            if tab_text != 'Comparison':
                # Find matching server key
                for server_key in self.server_groups.keys():
                    if tab_text == self.server_display_names[server_key] or 'Server' in tab_text:
                        self.main_notebook.tab(i, text=server_key)
                        break
        
        # Update server viewers
        for server_key in self.server_viewers:
            self.server_viewers[server_key].update_server_name(server_key)
        
        # Refresh displays
        self.update_status()
        messagebox.showinfo("Reset Complete", "All server names reset to defaults")
        
    def run_comparison(self):
        """Run full comparison analysis on selected servers"""
        if not self.validate_comparison():
            return
            
        selected_servers = self.get_selected_servers()
        
        self.comparison_text.delete(1.0, tk.END)
        self.comparison_text.insert(tk.END, "MULTI-SERVER COMPARISON ANALYSIS\n")
        self.comparison_text.insert(tk.END, "="*60 + "\n\n")
        
        # Basic statistics comparison
        self.comparison_text.insert(tk.END, "SERVER COMPARISON OVERVIEW\n")
        self.comparison_text.insert(tk.END, "-" * 30 + "\n")
        
        for server_key in selected_servers:
            stats = self.server_groups[server_key].get_stats()
            display_name = self.server_display_names[server_key]
            self.comparison_text.insert(tk.END, f"{display_name}: {stats['total_logs']} logs, {stats['errors']} errors, {stats['warnings']} warnings\n")
        self.comparison_text.insert(tk.END, "\n")
        
        # Run pairwise comparisons for timeline correlation
        self.comparison_text.insert(tk.END, "TIMELINE CORRELATIONS\n")
        self.comparison_text.insert(tk.END, "-" * 20 + "\n")
        
        time_window = float(self.time_window_var.get())
        found_correlations = False
        
        for i, server1 in enumerate(selected_servers):
            for server2 in selected_servers[i+1:]:
                logs1 = self.server_groups[server1].logs
                logs2 = self.server_groups[server2].logs
                
                timeline_correlations = ComparisonEngine.find_timeline_correlations(logs1, logs2, time_window)
                
                if timeline_correlations:
                    found_correlations = True
                    name1 = self.server_display_names[server1]
                    name2 = self.server_display_names[server2]
                    self.comparison_text.insert(tk.END, f"\n{name1} vs {name2}:\n")
                    
                    for correlation in timeline_correlations[:5]:  # Top 5 per pair
                        self.comparison_text.insert(tk.END, f"  Time: {correlation['time_bucket'].strftime('%Y-%m-%d %H:%M:%S')} UTC\n")
                        self.comparison_text.insert(tk.END, f"    {name1}: {correlation['server1_events']} events ({correlation['server1_errors']} errors)\n")
                        self.comparison_text.insert(tk.END, f"    {name2}: {correlation['server2_events']} events ({correlation['server2_errors']} errors)\n")
                        if correlation['time_offset_minutes'] != 0:
                            self.comparison_text.insert(tk.END, f"    Time offset: {correlation['time_offset_minutes']} minutes\n")
        
        if not found_correlations:
            self.comparison_text.insert(tk.END, "No significant timeline correlations found.\n")
        
        self.comparison_text.insert(tk.END, "\n")
        
        # Run message similarity for all pairs
        self.comparison_text.insert(tk.END, "MESSAGE SIMILARITY ANALYSIS\n")
        self.comparison_text.insert(tk.END, "-" * 30 + "\n")
        
        similarity_threshold = float(self.similarity_var.get())
        found_similarities = False
        
        for i, server1 in enumerate(selected_servers):
            for server2 in selected_servers[i+1:]:
                logs1 = self.server_groups[server1].logs
                logs2 = self.server_groups[server2].logs
                
                similar_messages = ComparisonEngine.find_similar_messages(
                    logs1, logs2, similarity_threshold, time_window
                )
                
                if similar_messages:
                    found_similarities = True
                    name1 = self.server_display_names[server1]
                    name2 = self.server_display_names[server2]
                    self.comparison_text.insert(tk.END, f"\n{name1} vs {name2}:\n")
                    
                    for correlation in similar_messages[:3]:  # Top 3 per pair
                        log1, log2 = correlation['log1'], correlation['log2']
                        self.comparison_text.insert(tk.END, f"  Similarity: {correlation['similarity']:.2f} | Time diff: {correlation['time_diff_minutes']:.1f} min\n")
                        self.comparison_text.insert(tk.END, f"    {name1}: {log1['full_message'][:80]}...\n")
                        self.comparison_text.insert(tk.END, f"    {name2}: {log2['full_message'][:80]}...\n\n")
        
        if not found_similarities:
            self.comparison_text.insert(tk.END, "No similar messages found above threshold.\n")
            
        # Switch to comparison tab
        self.main_notebook.select(self.comparison_frame)
        
    def run_timeline_correlation(self):
        """Focus on timeline correlation analysis for selected servers"""
        if not self.validate_comparison():
            return
            
        selected_servers = self.get_selected_servers()
        
        self.comparison_text.delete(1.0, tk.END)
        self.comparison_text.insert(tk.END, "TIMELINE CORRELATION ANALYSIS\n")
        self.comparison_text.insert(tk.END, "="*40 + "\n\n")
        
        time_window = float(self.time_window_var.get())
        total_correlations = 0
        
        for i, server1 in enumerate(selected_servers):
            for server2 in selected_servers[i+1:]:
                logs1 = self.server_groups[server1].logs
                logs2 = self.server_groups[server2].logs
                
                correlations = ComparisonEngine.find_timeline_correlations(logs1, logs2, time_window)
                
                name1 = self.server_display_names[server1]
                name2 = self.server_display_names[server2]
                
                if correlations:
                    total_correlations += len(correlations)
                    self.comparison_text.insert(tk.END, f"{name1} vs {name2} - Found {len(correlations)} correlations:\n\n")
                    
                    for j, correlation in enumerate(correlations, 1):
                        self.comparison_text.insert(tk.END, f"{j}. Time Period: {correlation['time_bucket'].strftime('%Y-%m-%d %H:%M:%S')} UTC\n")
                        self.comparison_text.insert(tk.END, f"   {name1} Activity: {correlation['server1_events']} events, {correlation['server1_errors']} errors\n")
                        self.comparison_text.insert(tk.END, f"   {name2} Activity: {correlation['server2_events']} events, {correlation['server2_errors']} errors\n")
                        
                        if correlation['time_offset_minutes'] != 0:
                            self.comparison_text.insert(tk.END, f"   Time Offset: {correlation['time_offset_minutes']} minutes\n")
                            
                        # Assess correlation strength
                        total_errors = correlation['server1_errors'] + correlation['server2_errors']
                        if total_errors > 0:
                            self.comparison_text.insert(tk.END, f"   ⚠️  Both servers had errors in this time period!\n")
                            
                        self.comparison_text.insert(tk.END, "\n")
                else:
                    self.comparison_text.insert(tk.END, f"{name1} vs {name2}: No timeline correlations found.\n\n")
        
        if total_correlations == 0:
            self.comparison_text.insert(tk.END, "No timeline correlations found between any selected servers.\n")
            
        self.main_notebook.select(self.comparison_frame)
        
    def run_message_similarity(self):
        """Focus on message similarity analysis across selected servers"""
        if not self.validate_comparison():
            return
            
        self.comparison_text.delete(1.0, tk.END)
        self.comparison_text.insert(tk.END, "MESSAGE SIMILARITY ANALYSIS\n")
        self.comparison_text.insert(tk.END, "="*35 + "\n\n")
        
        selected_servers = self.get_selected_servers()
        similarity_threshold = float(self.similarity_var.get())
        time_window = float(self.time_window_var.get())
        
        total_pairs = 0
        total_found = 0
        
        for i, server1 in enumerate(selected_servers):
            for server2 in selected_servers[i+1:]:
                total_pairs += 1
                logs1 = self.server_groups[server1].logs
                logs2 = self.server_groups[server2].logs
                
                similar_messages = ComparisonEngine.find_similar_messages(
                    logs1, logs2, similarity_threshold, time_window
                )
                
                name1 = self.server_display_names[server1]
                name2 = self.server_display_names[server2]
                
                if similar_messages:
                    total_found += len(similar_messages)
                    self.comparison_text.insert(tk.END, f"{name1} vs {name2} - Found {len(similar_messages)} similar message pairs:\n\n")
                    
                    for j, correlation in enumerate(similar_messages[:5], 1):
                        log1, log2 = correlation['log1'], correlation['log2']
                        self.comparison_text.insert(tk.END, f"{j}. Similarity: {correlation['similarity']:.3f} | Time diff: {correlation['time_diff_minutes']:.1f} min\n")
                        self.comparison_text.insert(tk.END, f"   {name1} [{log1['component']}] {log1['timestamp']}\n")
                        self.comparison_text.insert(tk.END, f"   {log1['full_message']}\n")
                        self.comparison_text.insert(tk.END, f"   {name2} [{log2['component']}] {log2['timestamp']}\n")
                        self.comparison_text.insert(tk.END, f"   {log2['full_message']}\n")
                        self.comparison_text.insert(tk.END, "-"*60 + "\n\n")
                else:
                    self.comparison_text.insert(tk.END, f"{name1} vs {name2}: No similar messages above threshold {similarity_threshold}.\n\n")
        
        if total_found == 0:
            self.comparison_text.insert(tk.END, "No similar messages found across selected servers.\n")
            self.comparison_text.insert(tk.END, "Try lowering the similarity threshold or increasing the time window.\n")
        
        self.main_notebook.select(self.comparison_frame)
        
    def run_component_comparison(self):
        """Compare component activity across selected servers"""
        if not self.validate_comparison():
            return
            
        self.comparison_text.delete(1.0, tk.END)
        self.comparison_text.insert(tk.END, "COMPONENT COMPARISON ANALYSIS\n")
        self.comparison_text.insert(tk.END, "="*40 + "\n\n")
        
        selected_servers = self.get_selected_servers()
        
        # Build union of all components across selected servers
        all_components = set()
        for sk in selected_servers:
            all_components.update(self.server_groups[sk].components)
        
        for component in sorted(all_components):
            self.comparison_text.insert(tk.END, f"Component: {component}\n")
            
            counts = []
            errors = []
            warnings = []
            
            for sk in selected_servers:
                sg = self.server_groups[sk]
                name = self.server_display_names[sk]
                comp_logs = [log for log in sg.logs if log['component'] == component]
                error_count = sum(1 for log in comp_logs if log['level'].lower() == 'error')
                warn_count = sum(1 for log in comp_logs if log['level'].lower() in ['warn', 'warning'])
                
                self.comparison_text.insert(tk.END, f"  {name}: {len(comp_logs)} logs, {error_count} errors, {warn_count} warnings\n")
                counts.append(len(comp_logs))
                errors.append(error_count)
                warnings.append(warn_count)
            
            # Highlight discrepancies
            if counts and (max(counts) - min(counts) > 5):
                self.comparison_text.insert(tk.END, f"  ⚠️  Significant activity difference between servers\n")
            if errors and (max(errors) - min(errors) > 3):
                self.comparison_text.insert(tk.END, f"  ⚠️  Significant error count difference between servers\n")
            
            # Highlight exclusive activity
            active_servers = sum(1 for c in counts if c > 0)
            if active_servers == 1 and len(selected_servers) > 1:
                only_idx = [i for i, c in enumerate(counts) if c > 0][0]
                only_server = self.server_display_names[selected_servers[only_idx]]
                self.comparison_text.insert(tk.END, f"  ⚠️  Component only active on {only_server}\n")
                
            self.comparison_text.insert(tk.END, "\n")
            
        self.main_notebook.select(self.comparison_frame)
        
    def run_server_analysis(self, server_name):
        """Run individual server analysis on the specified tab"""
        server_group = self.server_groups[server_name]
        if not server_group.logs:
            messagebox.showwarning("Warning", f"No logs loaded for {server_name}")
            return
        
        # Switch to the server's tab and run analysis
        if server_name in self.server_frames:
            self.main_notebook.select(self.server_frames[server_name])
        if server_name in self.server_viewers:
            self.server_viewers[server_name].run_timeline_analysis()
            
        
    def export_results(self):
        """Export comparison results"""
        if not self.comparison_text.get(1.0, tk.END).strip():
            messagebox.showwarning("Warning", "No comparison results to export")
            return
            
        file_path = filedialog.asksaveasfilename(
            title="Export Comparison Results",
            defaultextension=".txt",
            filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")]
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(self.comparison_text.get(1.0, tk.END))
                messagebox.showinfo("Success", f"Results exported to {file_path}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to export: {str(e)}")
                
    def convert_timezone(self, utc_timestamp):
        """Convert UTC timestamp to selected timezone"""
        tz_map = {
            "UTC": 0,
            "Eastern (EDT)": -4,  # UTC-4
            "Eastern (EST)": -5,  # UTC-5
            "Central (CDT)": -5,  # UTC-5
            "Central (CST)": -6,  # UTC-6
            "Mountain (MDT)": -6, # UTC-6
            "Mountain (MST)": -7, # UTC-7
            "Pacific (PDT)": -7,  # UTC-7
            "Pacific (PST)": -8   # UTC-8
        }
        
        selected_tz = self.timezone_var.get()
        offset_hours = tz_map.get(selected_tz, 0)
        
        return utc_timestamp + timedelta(hours=offset_hours)
    
    def get_timezone_name(self):
        """Get timezone abbreviation for display"""
        tz_names = {
            "UTC": "UTC",
            "Eastern (EDT)": "EDT", 
            "Eastern (EST)": "EST",
            "Central (CDT)": "CDT",
            "Central (CST)": "CST", 
            "Mountain (MDT)": "MDT",
            "Mountain (MST)": "MST",
            "Pacific (PDT)": "PDT",
            "Pacific (PST)": "PST"
        }
        
        selected_tz = self.timezone_var.get()
        return tz_names.get(selected_tz, "UTC")
    

class ServerViewer:
    """Individual server log viewer component"""
    def __init__(self, parent, server_name, main_app):
        self.parent = parent
        self.server_key = server_name  # Keep the key for data access
        self.server_name = server_name  # Display name, can be changed
        self.main_app = main_app
        self.server_group = main_app.server_groups[server_name]
        self.filtered_logs = []
        
        self.setup_widgets()
        
    def update_server_name(self, new_name):
        """Update the display name for this server"""
        self.server_name = new_name
        # Update the stats display
        self.refresh_display()
        
    def setup_widgets(self):
        # Toolbar
        toolbar = ttk.Frame(self.parent)
        toolbar.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(toolbar, text="Load Files", 
                  command=lambda: self.main_app.load_file(self.server_key)).pack(side=tk.LEFT, padx=5)
        ttk.Button(toolbar, text="Add Files", 
                  command=lambda: self.main_app.add_file(self.server_key)).pack(side=tk.LEFT, padx=5)
        ttk.Button(toolbar, text="Clear", 
                  command=lambda: self.main_app.clear_server(self.server_key)).pack(side=tk.LEFT, padx=5)
        
        # Server stats
        self.stats_var = tk.StringVar(value=f"{self.server_name}: No files loaded")
        ttk.Label(toolbar, textvariable=self.stats_var).pack(side=tk.RIGHT, padx=5)
        
        # Filters frame
        filter_frame = ttk.LabelFrame(self.parent, text="Filters")
        filter_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Time range filter
        time_frame = ttk.Frame(filter_frame)
        time_frame.pack(side=tk.LEFT, padx=10)
        ttk.Label(time_frame, text="Time Range:").pack(side=tk.LEFT)
        self.start_time = tk.StringVar()
        self.end_time = tk.StringVar()
        ttk.Entry(time_frame, textvariable=self.start_time, width=15).pack(side=tk.LEFT, padx=2)
        ttk.Label(time_frame, text="to").pack(side=tk.LEFT)
        ttk.Entry(time_frame, textvariable=self.end_time, width=15).pack(side=tk.LEFT, padx=2)
        
        # Component filter
        comp_frame = ttk.Frame(filter_frame)
        comp_frame.pack(side=tk.LEFT, padx=10)
        ttk.Label(comp_frame, text="Component:").pack(side=tk.LEFT)
        self.component_var = tk.StringVar()
        self.component_combo = ttk.Combobox(comp_frame, textvariable=self.component_var, width=12)
        self.component_combo.pack(side=tk.LEFT, padx=5)
        
        # Level filter
        level_frame = ttk.Frame(filter_frame)
        level_frame.pack(side=tk.LEFT, padx=10)
        ttk.Label(level_frame, text="Level:").pack(side=tk.LEFT)
        self.level_var = tk.StringVar()
        self.level_combo = ttk.Combobox(level_frame, textvariable=self.level_var, width=8)
        self.level_combo.pack(side=tk.LEFT, padx=5)
        
        # File filter
        file_frame = ttk.Frame(filter_frame)
        file_frame.pack(side=tk.LEFT, padx=10)
        ttk.Label(file_frame, text="File:").pack(side=tk.LEFT)
        self.file_var = tk.StringVar()
        self.file_combo = ttk.Combobox(file_frame, textvariable=self.file_var, width=12)
        self.file_combo.pack(side=tk.LEFT, padx=5)
        
        # Search
        search_frame = ttk.Frame(filter_frame)
        search_frame.pack(side=tk.LEFT, padx=10)
        ttk.Label(search_frame, text="Search:").pack(side=tk.LEFT)
        self.search_var = tk.StringVar()
        search_entry = ttk.Entry(search_frame, textvariable=self.search_var, width=15)
        search_entry.pack(side=tk.LEFT, padx=5)
        search_entry.bind('<Return>', lambda e: self.apply_filters())
        
        # Filter buttons
        button_frame = ttk.Frame(filter_frame)
        button_frame.pack(side=tk.LEFT, padx=10)
        ttk.Button(button_frame, text="Apply", command=self.apply_filters).pack(side=tk.LEFT, padx=2)
        ttk.Button(button_frame, text="Clear", command=self.clear_filters).pack(side=tk.LEFT, padx=2)
        
        # Timezone selector
        tz_frame = ttk.Frame(filter_frame)
        tz_frame.pack(side=tk.RIGHT, padx=10)
        ttk.Label(tz_frame, text="Timezone:").pack(side=tk.LEFT)
        tz_combo = ttk.Combobox(tz_frame, textvariable=self.main_app.timezone_var, width=12, 
                        values=["UTC", "Eastern (EDT)", "Eastern (EST)", "Central (CDT)", "Central (CST)", 
                               "Mountain (MDT)", "Mountain (MST)", "Pacific (PDT)", "Pacific (PST)"])
        tz_combo.pack(side=tk.LEFT, padx=5)
        tz_combo.bind('<<ComboboxSelected>>', self.main_app.on_timezone_change)
        
        # Analysis buttons frame
        analysis_frame = ttk.Frame(self.parent)
        analysis_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(analysis_frame, text="Timeline Analysis", command=self.run_timeline_analysis).pack(side=tk.LEFT, padx=2)
        ttk.Button(analysis_frame, text="Error Analysis", command=self.run_error_analysis).pack(side=tk.LEFT, padx=2)
        ttk.Button(analysis_frame, text="Health Analysis", command=self.run_health_analysis).pack(side=tk.LEFT, padx=2)
        ttk.Button(analysis_frame, text="Component Analysis", command=self.run_component_analysis).pack(side=tk.LEFT, padx=2)
        ttk.Button(analysis_frame, text="Generate Report", command=self.generate_report).pack(side=tk.LEFT, padx=2)
        
        # Export buttons
        export_frame = ttk.Frame(analysis_frame)
        export_frame.pack(side=tk.RIGHT, padx=10)
        ttk.Button(export_frame, text="Export Filtered", command=self.export_filtered).pack(side=tk.LEFT, padx=2)
        ttk.Button(export_frame, text="Export Analysis", command=self.export_analysis).pack(side=tk.LEFT, padx=2)
        
        # Paned window for log list and details
        paned_window = ttk.PanedWindow(self.parent, orient=tk.HORIZONTAL)
        paned_window.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Left panel - Log list
        left_panel = ttk.Frame(paned_window)
        
        # Log tree
        columns = ('timestamp', 'level', 'component', 'file', 'message')
        self.tree = ttk.Treeview(left_panel, columns=columns, show='headings', height=20)
        
        self.tree.heading('timestamp', text='Timestamp')
        self.tree.heading('level', text='Level')
        self.tree.heading('component', text='Component') 
        self.tree.heading('file', text='File')
        self.tree.heading('message', text='Message')
        
        self.tree.column('timestamp', width=180)
        self.tree.column('level', width=80)
        self.tree.column('component', width=120)
        self.tree.column('file', width=100)
        self.tree.column('message', width=300)
        
        # Scrollbars
        v_scrollbar = ttk.Scrollbar(left_panel, orient=tk.VERTICAL, command=self.tree.yview)
        h_scrollbar = ttk.Scrollbar(left_panel, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # Right panel - Details
        right_panel = ttk.Frame(paned_window)
        
        details_notebook = ttk.Notebook(right_panel)
        
        # Raw JSON tab
        raw_frame = ttk.Frame(details_notebook)
        self.raw_text = scrolledtext.ScrolledText(raw_frame, wrap=tk.WORD)
        self.raw_text.pack(fill=tk.BOTH, expand=True)
        details_notebook.add(raw_frame, text="Raw JSON")
        
        # Formatted tab
        formatted_frame = ttk.Frame(details_notebook)
        self.formatted_text = scrolledtext.ScrolledText(formatted_frame, wrap=tk.WORD)
        self.formatted_text.pack(fill=tk.BOTH, expand=True)
        details_notebook.add(formatted_frame, text="Formatted")
        
        # Metrics tab
        metrics_frame = ttk.Frame(details_notebook)
        self.metrics_text = scrolledtext.ScrolledText(metrics_frame, wrap=tk.WORD)
        self.metrics_text.pack(fill=tk.BOTH, expand=True)
        details_notebook.add(metrics_frame, text="Metrics")
        
        # Analysis tab
        analysis_frame = ttk.Frame(details_notebook)
        self.analysis_text = scrolledtext.ScrolledText(analysis_frame, wrap=tk.WORD)
        self.analysis_text.pack(fill=tk.BOTH, expand=True)
        details_notebook.add(analysis_frame, text="Analysis")
        
        details_notebook.pack(fill=tk.BOTH, expand=True)
        
        paned_window.add(left_panel, weight=2)
        paned_window.add(right_panel, weight=1)
        
        # Bind selection event
        self.tree.bind('<<TreeviewSelect>>', self.on_log_select)
        
    def refresh_display(self):
        """Refresh the display with current server data"""
        # Update stats
        stats = self.server_group.get_stats()
        self.stats_var.set(f"{self.server_name}: {stats['total_logs']} logs, {stats['files']} files, {stats['errors']} errors")
        
        # Update filter dropdowns
        self.component_combo['values'] = ['All'] + sorted(list(self.server_group.components))
        self.level_combo['values'] = ['All'] + sorted(list(self.server_group.log_levels))
        self.file_combo['values'] = ['All'] + sorted(list(self.server_group.loaded_files))
        
        # Reset filters if not set
        if not self.component_var.get():
            self.component_var.set('All')
        if not self.level_var.get():
            self.level_var.set('All')
        if not self.file_var.get():
            self.file_var.set('All')
            
        self.apply_filters()
        
    def apply_filters(self):
        """Apply all filters to log display"""
        self.filtered_logs = []
        
        # Get filter values
        component_filter = self.component_var.get()
        level_filter = self.level_var.get()
        file_filter = self.file_var.get()
        search_term = self.search_var.get().lower()
        start_time_str = self.start_time.get()
        end_time_str = self.end_time.get()
        
        # Parse time filters
        start_time = None
        end_time = None
        
        if start_time_str:
            try:
                start_time = datetime.fromisoformat(start_time_str.replace('Z', '+00:00'))
            except:
                try:
                    start_time = datetime.strptime(start_time_str, '%Y-%m-%d %H:%M:%S')
                except:
                    pass
                    
        if end_time_str:
            try:
                end_time = datetime.fromisoformat(end_time_str.replace('Z', '+00:00'))
            except:
                try:
                    end_time = datetime.strptime(end_time_str, '%Y-%m-%d %H:%M:%S')
                except:
                    pass
        
        # Apply all filters
        for log in self.server_group.logs:
            # Component filter
            if component_filter != 'All' and log['component'] != component_filter:
                continue
            
            # Level filter
            if level_filter != 'All' and log['level'] != level_filter:
                continue
            
            # File filter
            if file_filter != 'All' and log.get('file_name', '') != file_filter:
                continue
                
            # Time range filter
            if start_time and log['parsed_timestamp'] < start_time:
                continue
            if end_time and log['parsed_timestamp'] > end_time:
                continue
                
            # Search filter
            if search_term:
                searchable_text = (log['full_message'] + ' ' + 
                                 json.dumps(log['raw'])).lower()
                if search_term not in searchable_text:
                    continue
            
            self.filtered_logs.append(log)
            
        self.update_tree_view()
        
    def clear_filters(self):
        """Clear all filters"""
        self.component_var.set('All')
        self.level_var.set('All')
        self.file_var.set('All')
        self.start_time.set('')
        self.end_time.set('')
        self.search_var.set('')
        self.apply_filters()
        
    def update_tree_view(self):
        """Update tree view with filtered logs"""
        # Clear existing
        for item in self.tree.get_children():
            self.tree.delete(item)
            
        # Add filtered logs
        for log in self.filtered_logs:
            self.tree.insert('', tk.END, values=(
                log['timestamp'],
                log['level'],
                log['component'],
                log.get('file_name', 'unknown'),
                log['message']
            ), tags=(log['line_number'], log.get('file_name', 'unknown')))
            
        # Update status if exists
        if hasattr(self, 'stats_var'):
            total = len(self.server_group.logs)
            filtered = len(self.filtered_logs)
            stats = self.server_group.get_stats()
            self.stats_var.set(f"{self.server_name}: Showing {filtered} of {total} logs ({stats['files']} files, {stats['errors']} errors)")
            
    def on_log_select(self, event):
        """Handle log selection"""
        selection = self.tree.selection()
        if not selection:
            return
            
        item = selection[0]
        tags = self.tree.item(item, 'tags')
        line_number = int(tags[0])
        file_name = tags[1] if len(tags) > 1 else 'unknown'
        
        # Find the log entry
        selected_log = None
        for log in self.server_group.logs:
            if log['line_number'] == line_number and log.get('file_name', 'unknown') == file_name:
                selected_log = log
                break
                
        if selected_log:
            self.show_log_details(selected_log)
            
    def show_log_details(self, log_entry):
        """Show details of selected log entry in all tabs"""
        # Raw JSON
        self.raw_text.delete(1.0, tk.END)
        self.raw_text.insert(1.0, json.dumps(log_entry['raw'], indent=2))
        
        # Formatted view
        self.formatted_text.delete(1.0, tk.END)
        formatted = self.format_log_entry(log_entry)
        self.formatted_text.insert(1.0, formatted)
        
        # Metrics (if present)
        self.metrics_text.delete(1.0, tk.END)
        if 'monitoring' in log_entry['raw']:
            metrics = self.extract_metrics(log_entry['raw']['monitoring'])
            self.metrics_text.insert(1.0, metrics)
        else:
            self.metrics_text.insert(1.0, "No metrics data in this log entry")
            
    def format_log_entry(self, log_entry):
        """Format log entry for human reading"""
        raw = log_entry['raw']
        lines = []
        
        lines.append(f"Timestamp: {log_entry['timestamp']}")
        lines.append(f"Log Level: {log_entry['level']}")
        lines.append(f"Component: {log_entry['component']}")
        lines.append(f"Server: {log_entry['server_name']}")
        lines.append(f"File: {log_entry.get('file_name', 'unknown')}")
        lines.append(f"Message: {log_entry['full_message']}")
        lines.append("")
        
        # Add other relevant fields
        if 'event' in raw:
            lines.append(f"Event: {raw['event']}")
        if 'monitor' in raw:
            lines.append(f"Monitor: {raw['monitor']}")
        if 'service.name' in raw:
            lines.append(f"Service: {raw['service.name']}")
        if 'log.origin' in raw:
            origin = raw['log.origin']
            lines.append(f"Origin: {origin.get('function', '')} ({origin.get('file.name', '')}:{origin.get('file.line', '')})")
            
        return '\n'.join(lines)
        
    def extract_metrics(self, monitoring_data):
        """Extract and format metrics from monitoring data"""
        lines = []
        
        if 'metrics' in monitoring_data:
            metrics = monitoring_data['metrics']
            
            # System metrics
            if 'system' in metrics:
                sys_metrics = metrics['system']
                lines.append("=== SYSTEM METRICS ===")
                if 'load' in sys_metrics:
                    load = sys_metrics['load']
                    lines.append(f"Load Average: 1m={load.get('1', 'N/A')}, 5m={load.get('5', 'N/A')}, 15m={load.get('15', 'N/A')}")
                lines.append("")
                
            # Beat metrics
            if 'beat' in metrics:
                beat_metrics = metrics['beat']
                lines.append("=== BEAT METRICS ===")
                
                if 'cpu' in beat_metrics:
                    cpu = beat_metrics['cpu']
                    lines.append(f"CPU - Total: {cpu.get('total', {}).get('value', 'N/A')} ticks")
                    
                if 'memstats' in beat_metrics:
                    mem = beat_metrics['memstats']
                    lines.append(f"Memory - Alloc: {mem.get('memory_alloc', 0):,} bytes")
                    lines.append(f"Memory - Total: {mem.get('memory_total', 0):,} bytes")
                    
                if 'runtime' in beat_metrics:
                    runtime = beat_metrics['runtime']
                    lines.append(f"Goroutines: {runtime.get('goroutines', 'N/A')}")
                lines.append("")
                
            # Libbeat metrics
            if 'libbeat' in metrics:
                lib_metrics = metrics['libbeat']
                lines.append("=== LIBBEAT METRICS ===")
                
                if 'output' in lib_metrics and 'events' in lib_metrics['output']:
                    events = lib_metrics['output']['events']
                    lines.append(f"Output Events - Acked: {events.get('acked', 0)}, Active: {events.get('active', 0)}")
                    
                if 'pipeline' in lib_metrics and 'events' in lib_metrics['pipeline']:
                    pipeline = lib_metrics['pipeline']['events']
                    lines.append(f"Pipeline Events - Published: {pipeline.get('published', 0)}")
                    
        return '\n'.join(lines) if lines else "No metrics extracted"
            
    def run_timeline_analysis(self):
        """Run comprehensive timeline analysis for this server"""
        if not self.server_group.logs:
            messagebox.showwarning("Warning", f"No logs loaded for {self.server_name}")
            return
            
        self.analysis_text.delete(1.0, tk.END)
        self.analysis_text.insert(tk.END, f"{self.server_name.upper()} TIMELINE ANALYSIS\n")
        self.analysis_text.insert(tk.END, "="*50 + "\n\n")
        
        # Group logs by component and timestamp
        component_timeline = defaultdict(list)
        all_timestamps = []
        
        for log in self.server_group.logs:
            if log['parsed_timestamp'] != datetime.min:
                component_timeline[log['component']].append(log['parsed_timestamp'])
                all_timestamps.append(log['parsed_timestamp'])
        
        if not all_timestamps:
            self.analysis_text.insert(tk.END, "No valid timestamps found for analysis.\n")
            return
            
        all_timestamps.sort()
        
        # Overall timeline stats
        start_time = all_timestamps[0]
        end_time = all_timestamps[-1]
        duration = end_time - start_time
        
        self.analysis_text.insert(tk.END, f"Timeline Overview:\n")
        self.analysis_text.insert(tk.END, f"  Start: {self.main_app.convert_timezone(start_time).strftime('%Y-%m-%d %H:%M:%S')} {self.main_app.get_timezone_name()}\n")
        self.analysis_text.insert(tk.END, f"  End: {self.main_app.convert_timezone(end_time).strftime('%Y-%m-%d %H:%M:%S')} {self.main_app.get_timezone_name()}\n")
        self.analysis_text.insert(tk.END, f"  Duration: {duration}\n")
        self.analysis_text.insert(tk.END, f"  Total Log Entries: {len(self.server_group.logs)}\n\n")
        
        # Find gaps in logging (periods longer than 2 minutes with no logs)
        self.analysis_text.insert(tk.END, "Logging Gaps (> 2 minutes):\n")
        gaps_found = False
        for i in range(1, len(all_timestamps)):
            gap = all_timestamps[i] - all_timestamps[i-1]
            if gap > timedelta(minutes=2):
                gaps_found = True
                gap_start = self.main_app.convert_timezone(all_timestamps[i-1])
                gap_end = self.main_app.convert_timezone(all_timestamps[i])
                tz_name = self.main_app.get_timezone_name()
                self.analysis_text.insert(tk.END, f"  Gap: {gap_start.strftime('%Y-%m-%d %H:%M:%S')} to {gap_end.strftime('%Y-%m-%d %H:%M:%S')} {tz_name} (Duration: {gap})\n")
        
        if not gaps_found:
            self.analysis_text.insert(tk.END, "  No significant gaps found.\n")
        
        self.analysis_text.insert(tk.END, "\n")
        
        # Component activity periods
        self.analysis_text.insert(tk.END, "Component Activity:\n")
        for component in sorted(component_timeline.keys()):
            timestamps = sorted(component_timeline[component])
            if timestamps:
                comp_start = self.main_app.convert_timezone(timestamps[0])
                comp_end = self.main_app.convert_timezone(timestamps[-1])
                comp_count = len(timestamps)
                tz_name = self.main_app.get_timezone_name()
                self.analysis_text.insert(tk.END, f"  {component}:\n")
                self.analysis_text.insert(tk.END, f"    First: {comp_start.strftime('%Y-%m-%d %H:%M:%S')} {tz_name}\n")
                self.analysis_text.insert(tk.END, f"    Last:  {comp_end.strftime('%Y-%m-%d %H:%M:%S')} {tz_name}\n")
                self.analysis_text.insert(tk.END, f"    Count: {comp_count} entries\n")
        
    def run_error_analysis(self):
        """Run comprehensive error analysis for this server"""
        if not self.server_group.logs:
            messagebox.showwarning("Warning", f"No logs loaded for {self.server_name}")
            return
            
        self.analysis_text.delete(1.0, tk.END)
        self.analysis_text.insert(tk.END, f"{self.server_name.upper()} ERROR ANALYSIS\n")
        self.analysis_text.insert(tk.END, "="*50 + "\n\n")
        
        # Count errors by level and component
        error_levels = Counter()
        error_by_component = defaultdict(Counter)
        error_messages = Counter()
        error_timeline = []
        
        for log in self.server_group.logs:
            level = log['level'].lower()
            component = log['component']
            message = log['full_message'][:100]  # First 100 chars
            
            error_levels[level] += 1
            error_by_component[component][level] += 1
            
            if level in ['error', 'warn', 'warning']:
                error_messages[message] += 1
                if log['parsed_timestamp'] != datetime.min:
                    error_timeline.append((log['parsed_timestamp'], level, component, message))
        
        # Overall error stats
        total_errors = error_levels['error']
        total_warnings = error_levels.get('warn', 0) + error_levels.get('warning', 0)
        
        self.analysis_text.insert(tk.END, f"Error Summary:\n")
        self.analysis_text.insert(tk.END, f"  Total Errors: {total_errors}\n")
        self.analysis_text.insert(tk.END, f"  Total Warnings: {total_warnings}\n\n")
        
        # Log levels breakdown
        self.analysis_text.insert(tk.END, "Log Levels:\n")
        for level, count in error_levels.most_common():
            percentage = (count / len(self.server_group.logs)) * 100
            self.analysis_text.insert(tk.END, f"  {level.upper()}: {count} ({percentage:.1f}%)\n")
        
        self.analysis_text.insert(tk.END, "\n")
        
        # Errors by component
        self.analysis_text.insert(tk.END, "Errors by Component:\n")
        for component in sorted(error_by_component.keys()):
            comp_errors = error_by_component[component]
            error_count = comp_errors['error']
            warn_count = comp_errors.get('warn', 0) + comp_errors.get('warning', 0)
            if error_count > 0 or warn_count > 0:
                self.analysis_text.insert(tk.END, f"  {component}: {error_count} errors, {warn_count} warnings\n")
        
        self.analysis_text.insert(tk.END, "\n")
        
        # Most common error messages
        if error_messages:
            self.analysis_text.insert(tk.END, "Most Common Error/Warning Messages:\n")
            for msg, count in error_messages.most_common(10):
                self.analysis_text.insert(tk.END, f"  [{count}x] {msg}...\n")
        
        # Recent errors/warnings timeline
        if error_timeline:
            self.analysis_text.insert(tk.END, "\nRecent Errors/Warnings:\n")
            error_timeline.sort(reverse=True)  # Most recent first
            for timestamp, level, component, message in error_timeline[:20]:
                local_time = self.main_app.convert_timezone(timestamp)
                tz_name = self.main_app.get_timezone_name()
                self.analysis_text.insert(tk.END, f"  [{local_time.strftime('%H:%M:%S')} {tz_name}] {level.upper()} - {component}: {message}...\n")
    
    def run_health_analysis(self):
        """Run comprehensive health analysis for this server"""
        if not self.server_group.logs:
            messagebox.showwarning("Warning", f"No logs loaded for {self.server_name}")
            return
            
        self.analysis_text.delete(1.0, tk.END)
        self.analysis_text.insert(tk.END, f"{self.server_name.upper()} HEALTH ANALYSIS\n")
        self.analysis_text.insert(tk.END, "="*50 + "\n\n")
        
        # Extract metrics
        cpu_values = []
        memory_values = []
        load_values = []
        goroutine_counts = []
        event_counts = []
        error_rates = []
        
        for log in self.server_group.logs:
            if 'monitoring' in log['raw'] and 'metrics' in log['raw']['monitoring']:
                metrics = log['raw']['monitoring']['metrics']
                
                # CPU metrics
                if 'beat' in metrics and 'cpu' in metrics['beat']:
                    cpu_total = metrics['beat']['cpu'].get('total', {}).get('value', 0)
                    if cpu_total > 0:
                        cpu_values.append(cpu_total)
                
                # Memory metrics
                if 'beat' in metrics and 'memstats' in metrics['beat']:
                    memory_alloc = metrics['beat']['memstats'].get('memory_alloc', 0)
                    if memory_alloc > 0:
                        memory_values.append(memory_alloc / 1024 / 1024)  # Convert to MB
                
                # System load
                if 'system' in metrics and 'load' in metrics['system']:
                    load_1m = metrics['system']['load'].get('1', 0)
                    if load_1m > 0:
                        load_values.append(load_1m)
                
                # Goroutines
                if 'beat' in metrics and 'runtime' in metrics['beat']:
                    goroutines = metrics['beat']['runtime'].get('goroutines', 0)
                    if goroutines > 0:
                        goroutine_counts.append(goroutines)
                
                # Event processing
                if 'libbeat' in metrics and 'output' in metrics['libbeat'] and 'events' in metrics['libbeat']['output']:
                    events = metrics['libbeat']['output']['events']
                    acked = events.get('acked', 0)
                    total = events.get('total', 0)
                    if total > 0:
                        event_counts.append(acked)
                        error_rate = max(0, (total - acked) / total * 100)
                        error_rates.append(error_rate)
        
        # Analyze metrics
        def analyze_metric(values, name, unit=""):
            if not values:
                self.analysis_text.insert(tk.END, f"{name}: No data available\n")
                return
                
            avg_val = statistics.mean(values)
            min_val = min(values)
            max_val = max(values)
            
            if len(values) > 1:
                stdev = statistics.stdev(values)
                median_val = statistics.median(values)
                self.analysis_text.insert(tk.END, f"{name}:\n")
                self.analysis_text.insert(tk.END, f"  Average: {avg_val:.2f} {unit}\n")
                self.analysis_text.insert(tk.END, f"  Median:  {median_val:.2f} {unit}\n")
                self.analysis_text.insert(tk.END, f"  Min/Max: {min_val:.2f} - {max_val:.2f} {unit}\n")
                self.analysis_text.insert(tk.END, f"  Std Dev: {stdev:.2f} {unit}\n")
            else:
                self.analysis_text.insert(tk.END, f"{name}: {avg_val:.2f} {unit}\n")
            
            # Detect potential issues
            if name == "Memory Usage" and avg_val > 500:
                self.analysis_text.insert(tk.END, f"  ⚠️  High memory usage detected\n")
            elif name == "System Load (1m)" and avg_val > 2.0:
                self.analysis_text.insert(tk.END, f"  ⚠️  High system load detected\n")
            elif name == "Goroutines" and avg_val > 200:
                self.analysis_text.insert(tk.END, f"  ⚠️  High goroutine count detected\n")
            
            self.analysis_text.insert(tk.END, "\n")
        
        analyze_metric(memory_values, "Memory Usage", "MB")
        analyze_metric(load_values, "System Load (1m)")
        analyze_metric(goroutine_counts, "Goroutines")
        analyze_metric(event_counts, "Events Processed")
        analyze_metric(error_rates, "Event Error Rate", "%")
        
        # Overall health assessment
        self.analysis_text.insert(tk.END, "Health Assessment:\n")
        issues = []
        
        if memory_values and statistics.mean(memory_values) > 500:
            issues.append("High memory usage")
        if load_values and statistics.mean(load_values) > 2.0:
            issues.append("High system load")
        if error_rates and statistics.mean(error_rates) > 5:
            issues.append("High event error rate")
        if goroutine_counts and statistics.mean(goroutine_counts) > 200:
            issues.append("High goroutine count")
        
        if issues:
            self.analysis_text.insert(tk.END, f"  ⚠️  Issues detected: {', '.join(issues)}\n")
        else:
            self.analysis_text.insert(tk.END, "  ✅ No significant issues detected\n")
    
    def run_component_analysis(self):
        """Run comprehensive component analysis for this server"""
        if not self.server_group.logs:
            messagebox.showwarning("Warning", f"No logs loaded for {self.server_name}")
            return
            
        self.analysis_text.delete(1.0, tk.END)
        self.analysis_text.insert(tk.END, f"{self.server_name.upper()} COMPONENT ANALYSIS\n")
        self.analysis_text.insert(tk.END, "="*50 + "\n\n")
        
        # Analyze component activity patterns
        component_stats = defaultdict(lambda: {
            'first_seen': None,
            'last_seen': None,
            'total_logs': 0,
            'error_count': 0,
            'warning_count': 0,
            'info_count': 0,
            'active_periods': [],
            'status_changes': []
        })
        
        for log in self.server_group.logs:
            component = log['component']
            timestamp = log['parsed_timestamp']
            level = log['level'].lower()
            
            stats = component_stats[component]
            stats['total_logs'] += 1
            
            if timestamp != datetime.min:
                if stats['first_seen'] is None or timestamp < stats['first_seen']:
                    stats['first_seen'] = timestamp
                if stats['last_seen'] is None or timestamp > stats['last_seen']:
                    stats['last_seen'] = timestamp
            
            if level == 'error':
                stats['error_count'] += 1
            elif level in ['warn', 'warning']:
                stats['warning_count'] += 1
            elif level == 'info':
                stats['info_count'] += 1
            
            # Track status changes
            message = log['full_message'].lower()
            if 'started' in message or 'starting' in message:
                stats['status_changes'].append(('started', timestamp))
            elif 'stopped' in message or 'stopping' in message:
                stats['status_changes'].append(('stopped', timestamp))
            elif 'failed' in message or 'error' in message:
                stats['status_changes'].append(('error', timestamp))
        
        # Display component analysis
        for component in sorted(component_stats.keys()):
            stats = component_stats[component]
            
            self.analysis_text.insert(tk.END, f"Component: {component}\n")
            self.analysis_text.insert(tk.END, f"  Total Logs: {stats['total_logs']}\n")
            
            if stats['first_seen'] and stats['last_seen']:
                first_local = self.main_app.convert_timezone(stats['first_seen'])
                last_local = self.main_app.convert_timezone(stats['last_seen'])
                tz_name = self.main_app.get_timezone_name()
                duration = stats['last_seen'] - stats['first_seen']
                
                self.analysis_text.insert(tk.END, f"  Active Period: {first_local.strftime('%Y-%m-%d %H:%M:%S')} to {last_local.strftime('%Y-%m-%d %H:%M:%S')} {tz_name}\n")
                self.analysis_text.insert(tk.END, f"  Duration: {duration}\n")
            
            # Log level breakdown
            total_messages = stats['error_count'] + stats['warning_count'] + stats['info_count']
            if total_messages > 0:
                self.analysis_text.insert(tk.END, f"  Log Levels: {stats['info_count']} info, {stats['warning_count']} warnings, {stats['error_count']} errors\n")
                
                # Health indicator
                error_rate = (stats['error_count'] / total_messages) * 100
                if error_rate > 10:
                    self.analysis_text.insert(tk.END, f"  ⚠️  High error rate: {error_rate:.1f}%\n")
                elif error_rate == 0 and stats['warning_count'] == 0:
                    self.analysis_text.insert(tk.END, f"  ✅ Clean logs (no errors/warnings)\n")
            
            # Status changes
            if stats['status_changes']:
                self.analysis_text.insert(tk.END, f"  Status Changes:\n")
                for status, timestamp in sorted(stats['status_changes'])[-5:]:  # Last 5 changes
                    if timestamp != datetime.min:
                        local_time = self.main_app.convert_timezone(timestamp)
                        tz_name = self.main_app.get_timezone_name()
                        self.analysis_text.insert(tk.END, f"    {local_time.strftime('%H:%M:%S')} {tz_name}: {status}\n")
            
            self.analysis_text.insert(tk.END, "\n")
    
    def generate_report(self):
        """Generate a comprehensive analysis report for this server"""
        if not self.server_group.logs:
            messagebox.showwarning("Warning", f"No logs loaded for {self.server_name}")
            return
            
        self.analysis_text.delete(1.0, tk.END)
        self.analysis_text.insert(tk.END, f"{self.server_name.upper()} COMPREHENSIVE ANALYSIS REPORT\n")
        self.analysis_text.insert(tk.END, "="*70 + "\n")
        self.analysis_text.insert(tk.END, f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        self.analysis_text.insert(tk.END, f"Files Analyzed: {len(self.server_group.loaded_files)}\n")
        self.analysis_text.insert(tk.END, f"Total Log Entries: {len(self.server_group.logs)}\n\n")
        
        # Executive Summary
        self.analysis_text.insert(tk.END, "EXECUTIVE SUMMARY\n")
        self.analysis_text.insert(tk.END, "-" * 20 + "\n")
        
        # Count key metrics
        error_count = len([log for log in self.server_group.logs if log['level'].lower() == 'error'])
        warning_count = len([log for log in self.server_group.logs if log['level'].lower() in ['warn', 'warning']])
        components = len(self.server_group.components)
        
        # Time range
        timestamps = [log['parsed_timestamp'] for log in self.server_group.logs if log['parsed_timestamp'] != datetime.min]
        if timestamps:
            timestamps.sort()
            duration = timestamps[-1] - timestamps[0]
            self.analysis_text.insert(tk.END, f"Time Range: {duration}\n")
            
            # Look for significant gaps (potential outages)
            significant_gaps = 0
            for i in range(1, len(timestamps)):
                gap = timestamps[i] - timestamps[i-1]
                if gap > timedelta(minutes=5):
                    significant_gaps += 1
            
            self.analysis_text.insert(tk.END, f"Components Active: {components}\n")
            self.analysis_text.insert(tk.END, f"Errors Found: {error_count}\n")
            self.analysis_text.insert(tk.END, f"Warnings Found: {warning_count}\n")
            self.analysis_text.insert(tk.END, f"Potential Outages: {significant_gaps} gaps > 5 minutes\n\n")
            
            # Overall health status
            if error_count == 0 and warning_count < 10 and significant_gaps == 0:
                self.analysis_text.insert(tk.END, "OVERALL STATUS: ✅ HEALTHY\n")
            elif error_count > 0 or significant_gaps > 0:
                self.analysis_text.insert(tk.END, "OVERALL STATUS: ⚠️  ISSUES DETECTED\n")
            else:
                self.analysis_text.insert(tk.END, "OVERALL STATUS: ⚠️  WARNINGS PRESENT\n")
        
        self.analysis_text.insert(tk.END, "\n" + "="*70 + "\n\n")
        
        # Run all analyses and append
        self.analysis_text.insert(tk.END, "Generating detailed analysis...\n\n")
        
        try:
            # Save current position and run analyses
            analyses = [
                ("Timeline Analysis", self.run_timeline_analysis),
                ("Error Analysis", self.run_error_analysis), 
                ("Health Analysis", self.run_health_analysis),
                ("Component Analysis", self.run_component_analysis)
            ]
            
            for name, analysis_func in analyses:
                self.analysis_text.insert(tk.END, f"\n{'='*70}\n")
                self.analysis_text.insert(tk.END, f"{name.upper()}\n")
                self.analysis_text.insert(tk.END, f"{'='*70}\n")
                try:
                    analysis_func()
                except Exception as e:
                    self.analysis_text.insert(tk.END, f"Error running {name}: {str(e)}\n")
                    
        except Exception as e:
            self.analysis_text.insert(tk.END, f"Error generating comprehensive report: {str(e)}\n")
    
    def export_filtered(self):
        """Export filtered logs to JSON or text file"""
        if not self.filtered_logs:
            messagebox.showwarning("Warning", "No filtered logs to export")
            return
            
        file_path = filedialog.asksaveasfilename(
            title=f"Export {self.server_name} Filtered Logs",
            defaultextension=".json",
            filetypes=[("JSON Files", "*.json"), ("Text Files", "*.txt"), ("All Files", "*.*")]
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    if file_path.endswith('.json'):
                        # Export as JSON - include both raw data and processed info
                        export_data = []
                        for log in self.filtered_logs:
                            export_entry = {
                                'server_name': self.server_name,  # Use custom name
                                'file_name': log.get('file_name', 'unknown'),
                                'line_number': log['line_number'],
                                'timestamp': log['timestamp'],
                                'parsed_timestamp': log['parsed_timestamp'].isoformat() if log['parsed_timestamp'] != datetime.min else None,
                                'level': log['level'],
                                'component': log['component'],
                                'message': log['full_message'],
                                'raw_log': log['raw']
                            }
                            export_data.append(export_entry)
                        json.dump(export_data, f, indent=2, default=str)
                    else:
                        # Export as formatted text
                        f.write(f"{self.server_name} Filtered Log Export\n")
                        f.write("=" * 50 + "\n")
                        f.write(f"Exported: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
                        f.write(f"Total Entries: {len(self.filtered_logs)}\n\n")
                        
                        for log in self.filtered_logs:
                            f.write(f"[{log['timestamp']}] {log['level']} - {log['component']}\n")
                            f.write(f"File: {log.get('file_name', 'unknown')} (Line {log['line_number']})\n")
                            f.write(f"Message: {log['full_message']}\n")
                            f.write("-" * 80 + "\n")
                            
                messagebox.showinfo("Success", f"Exported {len(self.filtered_logs)} logs to {file_path}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to export filtered logs: {str(e)}")
    
    def export_analysis(self):
        """Export current analysis results to file"""
        analysis_content = self.analysis_text.get(1.0, tk.END).strip()
        if not analysis_content:
            messagebox.showwarning("Warning", "No analysis results to export")
            return
            
        file_path = filedialog.asksaveasfilename(
            title=f"Export {self.server_name} Analysis",
            defaultextension=".txt",
            filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")]
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(f"{self.server_name} Analysis Export\n")
                    f.write("=" * 50 + "\n")
                    f.write(f"Exported: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
                    f.write(analysis_content)
                    
                messagebox.showinfo("Success", f"Analysis results exported to {file_path}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to export analysis: {str(e)}")

def main():
    root = tk.Tk()
    app = MultiServerLogViewer(root)
    root.mainloop()

if __name__ == "__main__":
    main()
# Multi-Server Elastic Agent Log Analyzer

A comprehensive GUI application for analyzing and comparing Elastic Agent logs across multiple servers. This tool helps system administrators and engineers identify patterns, correlations, and issues in distributed Elastic Agent deployments.

## Features

###  Multi-Server Support
- **Dynamic Server Management**: Add, remove, and rename server tabs on-the-fly
- **Parallel Log Analysis**: Analyze logs from multiple servers simultaneously
- **Cross-Server Comparison**: Compare logs, timelines, and metrics across servers

###  Advanced Analysis
- **Timeline Analysis**: Identify logging gaps, active periods, and component lifecycles
- **Error Analysis**: Comprehensive error and warning categorization and trending
- **Health Monitoring**: System metrics analysis (CPU, memory, load, goroutines)
- **Component Analysis**: Per-component activity patterns and status tracking

###  Intelligent Filtering
- **Time Range Filtering**: Filter logs by specific time windows
- **Component Filtering**: Focus on specific Elastic Agent components
- **Log Level Filtering**: Filter by severity (info, warn, error, etc.)
- **Search Functionality**: Full-text search across log messages and metadata
- **File-based Filtering**: View logs from specific files only

### 🔗 Cross-Server Correlation
- **Timeline Correlation**: Find events occurring simultaneously across servers
- **Message Similarity**: Identify similar error patterns between servers
- **Component Comparison**: Compare component activity across the fleet

###  Timezone Support
- **Multiple Timezone Display**: Convert UTC timestamps to local timezones
- **Supported Timezones**: UTC, Eastern, Central, Mountain, Pacific (both Standard and Daylight time)

###  Export Capabilities
- **Filtered Log Export**: Export filtered results as JSON or text
- **Analysis Report Export**: Save comprehensive analysis reports
- **Comparison Results Export**: Export cross-server comparison findings

## Installation

### Prerequisites
- Python 3.7 or higher
- tkinter (usually included with Python)

### Required Libraries
The application uses only Python standard library modules:
- `tkinter` - GUI framework
- `json` - JSON log parsing
- `datetime` - Timestamp handling
- `pathlib` - File path operations
- `collections` - Data structures
- `statistics` - Statistical calculations
- `difflib` - Text similarity comparison
- `threading` - Background file loading

```

## Usage

### Getting Started
1. **Launch the Application**: Run the Python script to open the GUI
2. **Add Servers**: The application starts with Server A and Server B tabs. Add more servers via `Settings > Add New Server`
3. **Load Log Files**: Use `File` menu to load or add Elastic Agent log files to each server
4. **Analyze**: Use the various analysis tools to examine your logs

### Loading Log Files
- **Load to Server**: Clears existing logs and loads new file(s)
- **Add to Server**: Appends new log file(s) to existing data
- **Supported Formats**: JSON log files (typical Elastic Agent format)

### Individual Server Analysis
Each server tab provides:
- **Log Viewer**: Filterable table view of all log entries
- **Detail Panels**: Raw JSON, formatted view, metrics extraction
- **Analysis Tools**: Timeline, error, health, and component analysis
- **Export Options**: Export filtered logs or analysis results

### Cross-Server Comparison
Use the **Comparison** tab to:
- **Select Servers**: Choose which servers to include in comparison
- **Run Comparisons**: Execute timeline correlation, message similarity, or component analysis
- **Adjust Parameters**: Modify time windows and similarity thresholds
- **Export Results**: Save comparison findings for reporting

### Analysis Types

#### Timeline Analysis
- Identifies logging gaps and active periods
- Maps component lifecycle events
- Detects potential system outages or restarts

#### Error Analysis
- Categorizes errors and warnings by frequency
- Groups issues by component
- Tracks error patterns over time

#### Health Analysis
- Extracts system metrics from log entries
- Analyzes CPU usage, memory consumption, system load
- Monitors Elastic Agent-specific metrics (goroutines, event processing)

#### Component Analysis
- Tracks individual component status and activity
- Identifies components with high error rates
- Maps component startup/shutdown sequences

### Filtering and Search
- **Time Range**: Use ISO format (YYYY-MM-DD HH:MM:SS) or partial dates
- **Components**: Select from detected components
- **Log Levels**: Filter by severity
- **Search**: Full-text search across messages and metadata
- **File Filter**: Focus on specific log files

## File Format Support

The application expects Elastic Agent logs in JSON format, with each line containing a complete JSON object. Typical log entry structure:
```json
{
  "@timestamp": "2024-01-15T10:30:45.123Z",
  "log.level": "info",
  "message": "Component started successfully",
  "component": {
    "binary": "elastic-agent",
    "type": "beat"
  },
  "service.name": "elastic-agent",
  "monitoring": {
    "metrics": {
      "beat": {
        "cpu": {"total": {"value": 12345}},
        "memstats": {"memory_alloc": 67890}
      }
    }
  }
}
```

## Configuration

### Server Management
- **Add Servers**: `Settings > Add New Server`
- **Remove Servers**: `Settings > Remove Server > [Server Name]`
- **Rename Servers**: `Settings > Rename Server > [Server Name]`
- **Reset Names**: `Settings > Reset All Names`

### Comparison Settings
- **Time Window**: Minutes within which events are considered correlated (default: 5)
- **Similarity Threshold**: Text similarity threshold for message matching (default: 0.7)

### Timezone Settings
Available in each server tab's filter panel. Converts UTC timestamps to local time for display.


---

**Version**: 1.0  
**Author**: [Your Name]  
**Last Updated**: January 2024

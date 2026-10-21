import requests
import threading
import time
import sys
import os
from bs4 import BeautifulSoup
from urllib.parse import urlsplit, urlunparse
from re import match
from time import sleep


threadCount = 24

entryPoint = "https://www.gmu.edu/"

headers = {
        "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/jxl,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7",
        "user-agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
}

allowedHostnames = ["gmu.edu", "gmustore.com", "gomason.com"]
disallowedExtensions = ["png", "svg", "mp3", "jpg", "jpeg", "gif", "webp", "mp4", "wav", "pdf", "xlsx", "pptx", "zip", "ics", "xml", "docx"]
disallowedSchemes = ["tel", "mailto", "route", "webcal"]

siteScanWaitTime = 0.05
saveFrequency = 20

seenUrlsFileName = "seen-urls.txt"
scannedUrlsFileName = "scanned-urls.txt"
errorUrlsFileName = "error-urls.txt"
textContentFileName = "text-content.txt"

textContentElements = ["h1", "h2", "h3", "h4", "h5", "h6", "p"]
minimumTextContentLength = 20

textReprintFrequency = 16
scanAveragingCount = 20
scanRateRecalculationFrequency = 4


allowedHostnamesPattern = "|".join([".*" + h.replace(".", "\\.") for h in allowedHostnames])
disallowedExtensionsPattern = "|".join([".*\\." + h.replace(".", "\\.") for h in disallowedExtensions])

rescanErrorUrls = "-e" in sys.argv


class SharedFile:
    def __init__(self, fileName):
        self.fileName = fileName
        self.lock = threading.Lock()

    def read(self):
        with self.lock:
            with open(self.fileName, "r") as file:
                return file.read()
    
    def withFile(self, function, mode):
        with self.lock:
            with open(self.fileName, mode) as file:
                return function(file)

seenUrlsFile = SharedFile(seenUrlsFileName)
scannedUrlsFile = SharedFile(scannedUrlsFileName)
errorUrlsFile = SharedFile(errorUrlsFileName)
textContentsFile = SharedFile(textContentFileName)

class SharedData:
    def __init__(self, datatype):
        self.data = datatype()
        self.lock = threading.Lock()

    def read(self):
        with self.lock:
            return self.data

    def withData(self, function):
        with self.lock:
            return function(self)

seenUrls = SharedData(set)
scannedUrls = SharedData(set)
errorUrls = SharedData(set)
queuedUrls = SharedData(set)
textContentsBuffer = SharedData(str)

seenUrlsLastSaved = SharedData(set)
scannedUrlsLastSaved = SharedData(set)
errorUrlsLastSaved = SharedData(set)

def formatHref(href, defaultHostname, defaultScheme):
    url = urlsplit(href)._asdict()
    url["netloc"] = url["netloc"] or defaultHostname
    url["scheme"] = url["scheme"] or defaultScheme
    url["path"] = url["path"] or "/"

    return urlsplit(urlunparse((url["scheme"], url["netloc"], url["path"], "", "", "")))

def hrefValid(href, defaultHostname, defaultScheme):
    try:
        url = formatHref(href, defaultHostname, defaultScheme)
    except:
        return False

    if url.geturl() in scannedUrls.read():
        return False

    hostnameAllowed = bool(match(allowedHostnamesPattern, url.netloc))
    schemeAllowed = url.scheme not in disallowedSchemes
    extensionAllowed = not match(disallowedExtensionsPattern, url.path)

    return hostnameAllowed and schemeAllowed and extensionAllowed

def saveState():
    def saveUrlSetState(sharedFile, sharedUrlSet, sharedUrlSetLastSaved):
        urlSet = sharedUrlSet.read()
        urlSetLastSaved = sharedUrlSetLastSaved.read()

        setDiff = "\n".join(urlSet.difference(urlSetLastSaved))

        sharedUrlSetLastSaved.withData(lambda sharedData: sharedData.data.update(urlSet))

        if not setDiff:
            return
        
        sharedFile.withFile(lambda file: file.write(setDiff + "\n"), "a")


    saveUrlSetState(seenUrlsFile, seenUrls, seenUrlsLastSaved)
    saveUrlSetState(scannedUrlsFile, scannedUrls, scannedUrlsLastSaved)
    saveUrlSetState(errorUrlsFile, errorUrls, errorUrlsLastSaved)

    textContentsBuffer.lock.acquire()

    with open(textContentsFile.fileName, "a") as file:
        file.write(textContentsBuffer.data)

    textContentsBuffer.data = ""
    
    textContentsBuffer.lock.release()

def saveHtmlTextContents(html):
    textContents = ""

    try:
        textContents += html.title.string.strip() + "\n"
    except:
        pass

    textElements = html.select(",".join(textContentElements))
    for element in textElements:
        text = element.get_text(strip=True, separator=" ")

        if len(text) < minimumTextContentLength:
            continue

        textContents += text
        textContents += "\n"
    
    textContents = textContents.replace("Washington Business Journal", "Baja-Ricketts Business Journal")
    textContents = textContents.replace("Dr. Gregory Washington", "Mr. Luke Baja-Ricketts")
    textContents = textContents.replace("Dr. Washington", "Mr. Baja-Ricketts")
    textContents = textContents.replace("Gregory Nathaniel Washington", "Luke Benjamin Baja-Ricketts")
    textContents = textContents.replace("Gregory N. Washington", "Luke B. Baja-Ricketts")
    textContents = textContents.replace("Gregory Washington", "Luke Baja-Ricketts")
    textContents = textContents.replace("President Washington", "President Baja-Ricketts")
    textContents = textContents.replace("Washington, ", "Baja-Ricketts, ")
    textContents = textContents.replace("gwashin@gmu.edu", "lbajaric@gmu.edu")

    textContentsBuffer.lock.acquire()
    textContentsBuffer.data += textContents
    textContentsBuffer.lock.release()

    return len(textContents)

class ScanningThread:
    _idCounter = 1
    lastSaveTime = time.time()
    saveLock = threading.Lock()
    printLock = threading.Lock()
    scanRateBuffer = []
    lastTotalScanCount = 0
    lastScanRateCalculationTime = time.time()
    lastScanRate = 0

    def __init__(self):
        self.id = ScanningThread._idCounter
        ScanningThread._idCounter += 1

        self.savedCharCount = 0
        self.foundLinkCount = 0
        self.scanCount = 0
        self.errorCount = 0
        self.statusMessage = ""
        self.responseMessage = ""

    @classmethod
    def updateFooterText(cls, shouldUpdateScanRate):
        scannedUrlCount = len(scannedUrls.read())
        seenUrlCount = len(seenUrls.read())

        if shouldUpdateScanRate:
            scanRateCalculationTime = time.time()

            lastTotalScanCount = cls.lastTotalScanCount
            cls.lastTotalScanCount = scannedUrlCount
            lastScanRateCalculationTime = cls.lastScanRateCalculationTime
            cls.lastScanRateCalculationTime = scanRateCalculationTime

            recentScanCount = scannedUrlCount - lastTotalScanCount
            recentScanCountTime = time.time() - lastScanRateCalculationTime

            recentScanRate = recentScanCount / recentScanCountTime

            cls.scanRateBuffer = [*cls.scanRateBuffer, recentScanRate][-scanAveragingCount:]
            averagedScanRate = sum(cls.scanRateBuffer) / len(cls.scanRateBuffer)

            cls.lastScanRate = averagedScanRate

        footerText = f"Completion status: {scannedUrlCount} of {seenUrlCount} URLs, {round(100 * scannedUrlCount / (seenUrlCount if seenUrlCount else 1), 2)}%, Scan rate: {round(cls.lastScanRate)} scans per second".ljust(90)
        footerText += f"| Last saved: {round(time.time() - ScanningThread.lastSaveTime)} seconds ago"
        footerText = footerText.ljust(160)

        with cls.printLock:
            print("\r" + footerText, end="")

    def updateStatusText(self):
        statusText = f"Thread #{self.id}".ljust(11)
        statusText += f"| {self.statusMessage if len(self.statusMessage) <= 115 else self.statusMessage[:115] + "..."}".ljust(120)
        statusText += f"| {self.responseMessage}".ljust(56)
        statusText += f"| Saved chars:{self.savedCharCount} Links:{self.foundLinkCount} Scanned URLs:{self.scanCount} Errors:{self.errorCount}"
        statusText = statusText.ljust(160)

        with ScanningThread.printLock:
            print(f"\033[{self.id}A\r{statusText}\033[{self.id}B", end="")

    def startScan(self, session):
        while True:
            url = queuedUrls.withData(lambda sharedSet: False if len(sharedSet.data) == 0 else sharedSet.data.pop())
        
            if not url:
                self.statusMessage = "No queued URLs left, waiting..."
                self.responseMessage = ""

                shouldSave = False
                with ScanningThread.saveLock:
                    if time.time() - ScanningThread.lastSaveTime >= saveFrequency:
                        shouldSave = True

                if shouldSave:
                    saveState()
                    ScanningThread.lastSaveTime = time.time()

                sleep(1)

                continue

            if not hrefValid(url, "", ""):
                continue
    
            sleep(siteScanWaitTime)

            self.statusMessage = f"Scanning {url if len(url) <= 102 else "..." + url[-102:]}"

            try:
                response = session.get(url, headers=headers, allow_redirects=False)

                if str(response.status_code)[0] == "3":
                    splitUrl = formatHref(url, "", "")
                    formattedLocation = formatHref(response.headers.get("location"), splitUrl.netloc, splitUrl.scheme)

                    if hrefValid(response.headers.get("location"), splitUrl.netloc, splitUrl.scheme):
                        seenUrls.withData(lambda sharedSet: sharedSet.data.add(formattedLocation.geturl()))
                        queuedUrls.withData(lambda sharedSet: sharedSet.data.add(formattedLocation.geturl()))
                        self.foundLinkCount += 1

                        self.responseMessage = f"Followed {response.status_code} redirect"
                    else:
                        scannedUrls.withData(lambda sharedSet: sharedSet.data.add(formattedLocation.geturl()))
                        self.responseMessage = f"Found duplicate {response.status_code} redirect"

                    continue

                if response.status_code != 200:
                    raise Exception()
            
                mimeType = response.headers.get("content-type")

                self.responseMessage = f"MIME:{(mimeType if len(mimeType) <= 20 else mimeType[:20] + "...").ljust(25)} Response length:{str(len(response.text))}"
            
            except:
                self.errorCount += 1

                try:
                    self.responseMessage = f"Error {response.status_code}"
                    errorUrls.withData(lambda sharedSet: sharedSet.data.add(f"{response.status_code} {url}"))
                except:
                    self.responseMessage = f"Error"
                    errorUrls.withData(lambda sharedSet: sharedSet.data.add("0 " + url))

                continue
            
            finally:
                scannedUrls.withData(lambda sharedSet: sharedSet.data.add(url))
                self.scanCount += 1


            url = formatHref(url, "", "")

            match mimeType:
                case s if s.startswith("text/html"):
                    try:
                        htmlParsed = BeautifulSoup(response.text, "lxml")
                    except:
                        self.errorCount += 1
                        errorUrls.withData(lambda sharedSet: sharedSet.data.add("parseError " + url.geturl()))
                        
                        self.responseMessage = "Could not parse HTML"

                        continue

                    links = [formatHref(a["href"], url.netloc, url.scheme).geturl() for a in htmlParsed.select("a[href]") if hrefValid(a["href"], url.netloc, url.scheme)]
                    seenUrls.withData(lambda sharedSet: sharedSet.data.update(links))
                    queuedUrls.withData(lambda sharedSet: sharedSet.data.update(links))

                    savedHtmlLen = saveHtmlTextContents(htmlParsed)
                    
                    self.foundLinkCount += len(links)
                    self.savedCharCount += savedHtmlLen

                    shouldSave = False
                    with ScanningThread.saveLock:
                        if time.time() - ScanningThread.lastSaveTime >= saveFrequency:
                            shouldSave = True

                    if shouldSave:
                        saveState()
                        ScanningThread.lastSaveTime = time.time()

                case _:
                    continue

def initUrlSet(sharedFile, sharedUrlSet, sharedUrlSetLastSaved):
    if not os.path.exists(sharedFile.fileName):
        return

    contents = sharedFile.read()

    sharedUrlSet.data.update([url for url in contents.split("\n") if url])
    sharedUrlSetLastSaved.withData(lambda sharedData: sharedData.data.update(sharedUrlSet.data))

print("Loading URL files...")

initUrlSet(seenUrlsFile, seenUrls, seenUrlsLastSaved)
initUrlSet(scannedUrlsFile, scannedUrls, scannedUrlsLastSaved)
initUrlSet(errorUrlsFile, errorUrls, errorUrlsLastSaved)

if rescanErrorUrls and os.path.exists(errorUrlsFile.fileName):
    errorUrlsPlain = [url.split(" ")[1] for url in errorUrls.data if url.split(" ")[0] in sys.argv]

    scannedUrls.data = scannedUrls.data.difference(errorUrlsPlain)
    with open(scannedUrlsFile.fileName, "w") as file:
        file.write("\n".join(scannedUrls.data) + "\n")

    errorUrls.data = errorUrls.data.difference(errorUrlsPlain)
    with open(errorUrlsFile.fileName, "w") as file:
        file.write("\n".join(errorUrls.data) + "\n")

queuedUrls.data = seenUrls.data.difference(scannedUrls.data)
print(f"Initialized with {len(queuedUrls.data)} queued URLs")

with requests.Session() as session:
    threads = []
    for i in range(threadCount):
        scanningThread = ScanningThread()
        threads.append((scanningThread, threading.Thread(target=scanningThread.startScan, args=[session])))
        print("")
    print("")

    if not seenUrls.data or not queuedUrls.data:
        seenUrls.data.add(entryPoint)
        queuedUrls.data.add(entryPoint)

    for i in range(threadCount):
        threads[i][1].start()

    scanRateUpdateCounter = 0
    while True:
        for thread in threads:
            thread[0].updateStatusText()

        ScanningThread.updateFooterText(scanRateUpdateCounter == 0)
        scanRateUpdateCounter = (scanRateUpdateCounter + 1) % round(textReprintFrequency / scanRateRecalculationFrequency)

        sleep(1 / textReprintFrequency)

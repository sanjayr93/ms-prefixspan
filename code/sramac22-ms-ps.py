# CS 583 - MS-PrefixSpan Project 1
# Author - Sanjay Ramachandran

import math
from copy import deepcopy

# globals
table = str.maketrans("{", "-", "}<>")
MISTable = str.maketrans('', '', "MIS()")
S = []
SSupCount = {}
MIS = {}
MISCount = {}
SDC = math.inf
seqPatterns = {}

def removeAndAdd(remove: list, add, target):
    # for the set operation A - B U C on a list
    ind = 0
    for iSet in remove:
        for i in iSet:
            try:
                ind = target.index(i)
                target.pop(ind)
            except ValueError:
                pass
    if add not in target:
        target.insert(ind, add)
        del target[:ind]
    return target

def addAndRemove(add: list, remove, target):
    # for the set operation A U B - C on a list
    ind = len(target)
    try:
        ind = target.index(remove)
        target.pop(ind)
    except ValueError:
        pass
    finally:
        for i in add:
            target.insert(ind, i)
            ind += 1
    return target

def supportCount(itemSet: list, tMap: dict, db=None, prefix=None):
    # for partially counting the support count of an itemset
    if db == None:
        for item in itemSet:
            tMap[item] = tMap.get(item, 0) + 1
    else:
        for seq in db:
            for item in itemSet:
                for iset in seq:
                    flag = False
                    if "_" in iset:
                        flag = True
                        iset = addAndRemove(prefix, "_", iset.copy())
                    if set(item).issubset(set(iset)):
                        if (not flag) or len(item) > 1:
                            tMap[tuple(item)] = tMap.get(tuple(item), 0) + 1
                            break

def readData(file, supportDict: dict):
    # Read input sequence database in to list data structure
    itemSet = set()
    def addToSet(item):
        nonlocal itemSet
        item = item.strip()
        itemSet.add(item)
        return item
    for line in file:
        S.append([[addToSet(item) for item in elem.strip().split(",")]
                  for elem in line.translate(table).split("-") if len(elem) > 0])
        supportCount(itemSet, supportDict)
        itemSet.clear()

def readMIS(file, N):
    # Read MIS and SDC parameters from params.txt
    global SDC
    for line in file:
        if "MIS" in line:
            temp = line.split("=")
            value = float(temp[1].strip())
            item = temp[0].strip().translate(MISTable)
            MIS[item] = value
            MISCount[item] = math.ceil(value * N)
        elif "SDC" in line:
            SDC = float(line.split("=")[1].strip())

def initSort():
    # sort frequent items based on their MIS values
    i = []
    for item in SSupCount.keys():
        if SSupCount[item] >= MISCount[item]:
            i.append(item)
    return sorted(i, key = lambda item: MIS[item])

def isIkinSeq(ik, seq):
    # checks if ik is in the sequence or not
    for iSet in seq:
        if ik in iSet:
            return True
    return False

def sdcCheck(val1, val2):
    return abs(val1 - val2) > SDC

def getSk(ik):
    # Create Sk from Sequence Database based on ik
    Sk = []
    for seq in S:
        kSeq = []
        if isIkinSeq(ik, seq):
            for iSet in seq:
                remElem = []
                copy = iSet.copy()
                for j in copy:
                    if sdcCheck((SSupCount[j]/len(S)), (SSupCount[ik]/len(S))):
                        remElem.append(j)
                for e in remElem:
                    copy.remove(e)
                if len(copy) > 0:
                    kSeq.append(copy)
            Sk.append(kSeq)
    return Sk

def updateS(ik):
    # removes ik from S
    for seq in S:
        for iSet in seq:
            if ik in iSet:
                iSet.remove(ik)

def SDCCheck2(sPatt):
    # finds the minsup and maxsup in a sequence to check the SDC constraint
    minS = math.inf
    maxS = -math.inf
    for iSet in sPatt:
        for i in iSet:
            val = SSupCount.get(i, 0)
            if val < minS:
                minS = val
            if val > maxS:
                maxS = val
    return abs((maxS/len(S))-(minS/len(S))) <= SDC

def getkeysFromSet(lastPrfxSet, iset):
    keys = []
    for item in iset:
        if item != "_":
            if "_" in iset:
                copy = lastPrfxSet.copy()
                copy.append(item)
                keys.append(copy)
            else:
                keys.append([item])
    return keys

def getSP(ik, prefix, item):
    # generate the sequence pattern based on the new frequent item and the prefix
    seqPatt = []
    if len(prefix[0]) > 0:
        seqPatt.extend(deepcopy(prefix))
    if len(item) > 1:
        for i in item:
            if i not in seqPatt[-1]:
                seqPatt[-1].append(i)
    else:
        seqPatt.append(item)
    return isIkinSeq(ik, seqPatt), seqPatt

def checkSupAndik(ik, prefix, lastISet, skpSeq, supCount, minsup):
    flag = False
    for iset in prefix:
        if ik in iset:
            flag = True
            break
    flag = flag or ik in lastISet
    remInd = []
    for i, iSet in enumerate(skpSeq):
        flag = flag or ik in iSet
    return len(skpSeq) > 0 and flag

def getSkProj(prefix, lastISet, ik, Sk, supCount, minsup):
    # generates the projection database based on the last itemset of the prefix
    SkProj = []
    for seq in Sk:
        skpSeq = []
        ind = -1
        for i, iset in enumerate(seq):
            flag = False
            if "_" in iset and len(lastISet) > 1: # _ replaced only when we look for <(ab)> projection in <a>-proj db
                # iset = prefix | iset - {"_"} # for creating ab-proj - if itemset has (_bc) -> abc - from this _c
                iset = addAndRemove(prefix[-1], "_", iset.copy())
                flag = True
            if "_" not in iset and set(lastISet).issubset(set(iset)):
                if len(iset) > len(lastISet): # in case (_c) and we search for c, shudnt add (__) in skpseq
                    # skpSeq.append(((iset - prefix) - lastISet) | {"_"})
                    if flag:
                        skpSeq.append(removeAndAdd([prefix[-1], lastISet], "_", iset.copy()))
                    else:
                        skpSeq.append(removeAndAdd([lastISet], "_", iset.copy()))
                ind = i
                break
        if ind > -1 and ind < len(seq) - 1:
            sseq = deepcopy(seq)
            skpSeq.extend(sseq[ind+1:])
        if ind > -1 and checkSupAndik(ik, prefix, lastISet, skpSeq, supCount, minsup):
            SkProj.append(skpSeq)
    return SkProj

def patternLen(pattern):
    l = 0
    for iset in pattern:
        l += len(iset)
    return l

def rPrefixSpan(prefix, ik, Sk, minsup):
    supCount = {}
    itemSet = []
    for seq in Sk:
        for iSet in seq:
            keys = getkeysFromSet(prefix[-1], iSet)
            for key in keys:
                if key not in itemSet:
                    itemSet.append(key)
    supportCount(itemSet, supCount, Sk, prefix[-1])
    itemSet.clear()
    for item, count in supCount.items():
        if count >= minsup:
            flag, seqPatt = getSP(ik, prefix, list(list(item)))
            flag2 = SDCCheck2(seqPatt)
            if flag and flag2:
                ll = patternLen(seqPatt)
                value = seqPatterns.get(ll, [])
                value.append((seqPatt, count))
                seqPatterns[ll] = value
            if flag2:
                rPrefixSpan(seqPatt, ik, getSkProj(prefix, seqPatt[-1], ik, Sk, supCount, minsup), minsup)

def clear(flag=False):
    seqPatterns.clear()
    if flag:
        S.clear()
        SSupCount.clear()
        MIS.clear()
        MISCount.clear()
        SDC = math.inf

def MSPS():
    clear()
    Ik = initSort()
    for ik in Ik:
        Sk = getSk(ik)
        rPrefixSpan([[]], ik, Sk, MISCount[ik])
        updateS(ik)

def formatOp(iList):
    return str(iList).replace("[[", "<{").replace("[", "{").replace("]]", " }>").replace("], ", " }").replace(",", "").replace("'", "")

if __name__ == "__main__":
    clear(True)
    paths = input("Enter the paths the data and param files separated by spaces : path_to_data path_to_params : \n").split()
    if len(paths) != 2:
        print("Terminating.. Please enter both file names in the same order separated by a space")
        exit()
    with open(paths[0], "r") as f:
        readData(f, SSupCount)
    with open(paths[1], "r") as f:
        readMIS(f, len(S))
    MSPS()
    with open("output.txt", "w") as opf:
        for i in range(1, len(seqPatterns) + 1):
            patterns = seqPatterns[i]
            opf.write("The number of length {0} sequential patterns is {1}\n".format(i, len(patterns)))
            for patt, count in patterns:
                opf.write("Pattern : {0}:Count={1}\n".format(formatOp(patt), count))

# ######
# Sample input
# ######

# Enter the paths the data and param files separated by spaces : path_to_data path_to_params :
# input.txt params.txt
#include <cstdio>
#include <iostream>
#include <set>
#include <map>
#include <stack>
#include <string>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

int POS_INFINITY = INT_MAX;
int NEG_INFINITY = INT_MIN;

struct DataInfo {
    int min = POS_INFINITY;
    int max = NEG_INFINITY;
    bool initialized = false;
};

int MAX_BOUND = 10;
int MIN_BOUND = -10;

typedef std::map<Instruction *, DataInfo> BBANALYSIS;

bool fixPointReached(BBANALYSIS oldAnalysisMap, BBANALYSIS currentBlockAnalysis);

BBANALYSIS updateBoundValues(BBANALYSIS bbAnalysis);

BBANALYSIS updateBBAnalysis(BasicBlock * BB, BBANALYSIS analysis);

std::string getSimpleNodeLabel(const BasicBlock *Node);

DataInfo evaluateOperators(std::string opCode, DataInfo obj1, DataInfo obj2);

void printAnalysisMap(std::map<std::string, BBANALYSIS> analysisMap);

int main(int argc, char **argv) {
    static LLVMContext Context;
    SMDiagnostic Err;

    std::unique_ptr<Module> M = parseIRFile(argv[1], Err, Context);
    if (M == nullptr) {
        fprintf(stderr, "error: failed to load LLVM IR file \"%s\"", argv[1]);
        return EXIT_FAILURE;
    }

    Function * F = M->getFunction("main");

    std::map<std::string, BBANALYSIS> analysisMap;
    for (auto &BB : *F) {
        BBANALYSIS emptyMap;
        analysisMap[getSimpleNodeLabel(&BB)] = emptyMap;
    }

    std::stack<BasicBlock *> traversalStack;
    BasicBlock* entryBB = &F->getEntryBlock();
    traversalStack.push(entryBB);

    std::cout<<traversalStack.empty()<<std::endl;

    while (!traversalStack.empty()) {
        BasicBlock* BB = traversalStack.top();
        traversalStack.pop();
        BBANALYSIS updatedCurrentBlockAnalysis = updateBBAnalysis(BB, analysisMap[getSimpleNodeLabel(BB)]);
        BBANALYSIS currentBlockAnalysis = updateBoundValues(updatedCurrentBlockAnalysis);
        analysisMap[getSimpleNodeLabel(BB)] = currentBlockAnalysis;

        const TerminatorInst *TInst = BB->getTerminator();
        int NSucc = TInst->getNumSuccessors();
        for (int i = 0; i < NSucc; ++i) {
            BasicBlock * Succ = TInst->getSuccessor(i);
            BBANALYSIS oldAnalysisMap = analysisMap[getSimpleNodeLabel(Succ)];

            if (!fixPointReached(oldAnalysisMap, currentBlockAnalysis)) {
                analysisMap[getSimpleNodeLabel(Succ)] = currentBlockAnalysis;
                traversalStack.push(Succ);
            }
        }
    }
    printAnalysisMap(analysisMap);
    return 0;
}

bool fixPointReached(BBANALYSIS oldAnalysisMap, BBANALYSIS currentBlockAnalysis) {
    if (oldAnalysisMap.empty() || oldAnalysisMap.size() != currentBlockAnalysis.size())
        return false;
    for (auto &it : currentBlockAnalysis) {
        DataInfo obj1 = oldAnalysisMap[it.first];
        DataInfo obj2 = it.second;
        if (obj1.min != obj2.min || obj1.max != obj2.max || obj1.initialized != obj2.initialized)
            return false;
    }
    return true;
}

BBANALYSIS updateBoundValues(BBANALYSIS bbAnalysis) {
    for (auto &x : bbAnalysis) {
        if(x.second.min < MIN_BOUND) x.second.min = NEG_INFINITY;
        if(x.second.max > MAX_BOUND) x.second.max = POS_INFINITY;
    }
    return bbAnalysis;
}

BBANALYSIS updateBBAnalysis(BasicBlock* BB, BBANALYSIS analysis) {
    for (auto &I: *BB) {
        if (isa<AllocaInst>(I)) {
            Instruction* inst = dyn_cast<Instruction>(&I);
            if (analysis.find(inst)== analysis.end()) {
                DataInfo obj;
                analysis[inst] = obj;
            }
        } else if (isa<LoadInst>(I)) {
            Instruction* inst = dyn_cast<Instruction>(&I);
            Instruction* operand = llvm::dyn_cast<AllocaInst>(I.getOperand(0));
            DataInfo obj = analysis.find(operand)->second;

            if (analysis.find(operand)== analysis.end()) {
                analysis[inst] = obj;
            } else {
                analysis[inst] = obj;
            }
        } else if (isa<StoreInst>(I)) {
            Value* v = I.getOperand(0);
            Instruction* source = llvm::dyn_cast<AllocaInst>(v);
            Instruction* target = llvm::dyn_cast<AllocaInst>(I.getOperand(1));

            if (isa<ConstantInt>(v)) {
                auto *constant = dyn_cast<ConstantInt>(v);
                int val = constant->getSExtValue();
                DataInfo obj;

                obj.min = val < obj.min ? val : NEG_INFINITY;
                obj.max = val > obj.max ? val : POS_INFINITY;
                obj.initialized = true;

                if (analysis.find(target)== analysis.end()) {
                    analysis[target] = obj;
                } else {
                    DataInfo previousObj = analysis[target];
                    if (previousObj.min<obj.min) {
                        obj.min = previousObj.min;
                    } else if (previousObj.max > obj.max) {
                        obj.max = previousObj.max;
                    }
                    analysis[target] = obj;
                }
            } else {
                DataInfo obj = analysis.find(source)->second;
                if (analysis.find(target)== analysis.end()) {
                    analysis[target] = obj;
                } else {
                    analysis[target] = obj;
                }
            }
        } else if (isa<BinaryOperator>(I)) {
            std::string opcode = I.getOpcodeName();
            Instruction *inst = dyn_cast<Instruction>(&I);

            Value *op1 = I.getOperand(0);
            Value *op2 = I.getOperand(1);
            DataInfo value1;
            DataInfo value2;
            int val1, val2;

            if (ConstantInt *CI = dyn_cast<ConstantInt>(op1)) {
                val1 = CI->getSExtValue();
                value1.min = val1;
                value1.max = val1;
                value1.initialized = true;
            } else {
                value1 = analysis.find(dyn_cast<Instruction>(op1))->second;
            }

            if (ConstantInt *CI = dyn_cast<ConstantInt>(op2)){
                val2 = CI->getSExtValue();
                value2.min = val2;
                value2.max = val2;
                value2.initialized = true;
            } else {
                value2 = analysis.find(dyn_cast<Instruction>(op2))->second;
            }
            DataInfo evaluationValue = evaluateOperators(opcode, value1, value2);
            if (analysis.find(inst)== analysis.end()) {
                analysis[inst] = evaluationValue;
            } else {
                analysis[inst] = evaluationValue;
            }
        }
    }
    return analysis;
}

DataInfo evaluateOperators(std::string opCode, DataInfo obj1, DataInfo obj2) {
    DataInfo obj;
    obj.initialized = false;
    if (!obj1.initialized || !obj2.initialized) return obj;
    if (obj1.initialized && obj2.initialized) obj.initialized = true;

    if (opCode.compare("add") == 0) {
        obj.min = obj1.min + obj2.min;
        obj.max = obj1.max + obj2.max;
    } else if (opCode.compare("sub") == 0) {
        obj.min = obj1.min - obj2.min;
        obj.max = obj1.max - obj2.max;
    } /*else if (opCode.compare("mul") == 0) {
        obj.min = obj1.min * obj2.min;
        obj.max = obj1.max * obj2.max;`
        obj.min = MIN(obj.min, obj.max);
        obj.max = MAX(obj.min, obj.max);
    } else if (opCode.compare("udiv") == 0 || opCode.compare("sdiv") == 0) {
        obj.min = obj1.min / obj2.max;
        obj.max = obj1.max / obj2.min;
        obj.min = MIN(obj.min, obj.max);
        obj.max = MAX(obj.min, obj.max);
    } else if (opCode.compare("urem") == 0 || opCode.compare("srem") == 0) {
        obj.min = 0;
        obj.max = obj2.max - 1;
    } else {
        printf("Unsupported operations");
    }*/
    return obj;
}

// Printing Basic Block Label
std::string getSimpleNodeLabel(const BasicBlock *Node) {
    if (!Node->getName().empty())
        return Node->getName().str();
    std::string Str;
    raw_string_ostream OS(Str);
    Node->printAsOperand(OS, false);
    return OS.str();
}

std::string getInstructionLabel(const Instruction *Node) {
    if (!Node->getName().empty())
        return Node->getName().str();
    std::string Str;
    raw_string_ostream OS(Str);
    Node->printAsOperand(OS, false);
    return OS.str();
}

void printAnalysisMap(std::map<std::string, BBANALYSIS> analysisMap) {
    for (auto &row : analysisMap) {
        std::string BBLabel = row.first;
        BBANALYSIS bbAnalysis = row.second;
        errs() << BBLabel << ":\n";
        for (auto &x : bbAnalysis) {
            std::string min = x.second.min == NEG_INFINITY ? "-Infinity" : std::to_string(x.second.min);
            std::string max = x.second.max == POS_INFINITY ? "+Infinity" : std::to_string(x.second.max);
            std::cout << getInstructionLabel(x.first) << '[' << min << ',' << max << ']' << std::endl;
        }
        errs() << "\n";
    }
}
//
// Created by Kritartha Ghosh on 2019-05-01.
//

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
    int min = NEG_INFINITY;
    int max = POS_INFINITY;
    bool initialized = false;
};

int MAX_BOUND = 50;
int MIN_BOUND = -50;

typedef std::map<Instruction *, DataInfo> BBANALYSIS;

bool fixPointReached(BBANALYSIS oldAnalysisMap, BBANALYSIS currentBlockAnalysis);

BBANALYSIS unionAnalysis(BBANALYSIS bbanalysis1, BBANALYSIS bbanalysis2);

BBANALYSIS updateBoundValues(BBANALYSIS bbAnalysis);

BBANALYSIS updateBBAnalysis(BasicBlock * BB, BBANALYSIS analysis);

std::string getSimpleNodeLabel(const BasicBlock *Node);

DataInfo evaluateOperators(std::string opCode, DataInfo obj1, DataInfo obj2);

void printAnalysisMap(std::map<std::string, BBANALYSIS> analysisMap);

std::string getInstructionLabel(const Instruction *Node);

std::set<std::pair <std::string,int>> getMaxSeparation(BBANALYSIS bbAnalysis);

bool getBranches(BBANALYSIS bbAnalysis, const ICmpInst* I, bool trueBranch);

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

        // Looping through each instruction and updating interval values of each variable.
        BBANALYSIS updatedCurrentBlockAnalysis = updateBBAnalysis(BB, analysisMap[getSimpleNodeLabel(BB)]);

        // Widening operator is applied.
        BBANALYSIS currentBlockAnalysis = updateBoundValues(updatedCurrentBlockAnalysis);
        analysisMap[getSimpleNodeLabel(BB)] = currentBlockAnalysis;

        // Passing the interval values to the children.
        const TerminatorInst *TInst = BB->getTerminator();
        int NSucc = TInst->getNumSuccessors();
        if (NSucc == 0) continue;

        if(NSucc == 2) {
            const ICmpInst *CmpInst = llvm::dyn_cast<ICmpInst>(TInst->getPrevNode());
            if(getBranches(currentBlockAnalysis, CmpInst, true)) {
                BasicBlock * Succ = TInst->getSuccessor(0);
                BBANALYSIS oldAnalysisMap = analysisMap[getSimpleNodeLabel(Succ)];
                BBANALYSIS newAnalysisMap = unionAnalysis(oldAnalysisMap, currentBlockAnalysis);

                if (!fixPointReached(oldAnalysisMap, newAnalysisMap)) {
                    analysisMap[getSimpleNodeLabel(Succ)] = newAnalysisMap;
                    traversalStack.push(Succ);
                }
            }

            if(getBranches(currentBlockAnalysis, CmpInst, false)) {
                BasicBlock * Succ = TInst->getSuccessor(1);
                BBANALYSIS oldAnalysisMap = analysisMap[getSimpleNodeLabel(Succ)];
                BBANALYSIS newAnalysisMap = unionAnalysis(oldAnalysisMap, currentBlockAnalysis);

                if (!fixPointReached(oldAnalysisMap, newAnalysisMap)) {
                    analysisMap[getSimpleNodeLabel(Succ)] = newAnalysisMap;
                    traversalStack.push(Succ);
                }
            }
        } else if(NSucc == 1) {
            BasicBlock * Succ = TInst->getSuccessor(0);
            BBANALYSIS oldAnalysisMap = analysisMap[getSimpleNodeLabel(Succ)];
            BBANALYSIS newAnalysisMap = unionAnalysis(oldAnalysisMap, currentBlockAnalysis);

            if (!fixPointReached(oldAnalysisMap, newAnalysisMap)) {
                analysisMap[getSimpleNodeLabel(Succ)] = newAnalysisMap;
                traversalStack.push(Succ);
            }
        }
    }
    printAnalysisMap(analysisMap);
    return 0;
}

BBANALYSIS unionAnalysis(BBANALYSIS bbanalysis1, BBANALYSIS bbanalysis2) {
    BBANALYSIS mergedAnalysis;

    for(auto &x : bbanalysis1) {
        if(bbanalysis2.find(x.first) != bbanalysis2.end()){
            DataInfo obj;
            obj.min = std::min(x.second.min, bbanalysis2[x.first].min);
            obj.max = std::max(x.second.max, bbanalysis2[x.first].max);
            mergedAnalysis[x.first] = obj;
        } else mergedAnalysis[x.first] = x.second;
    }

    for(auto &x : bbanalysis2) {
        if(mergedAnalysis.find(x.first) == mergedAnalysis.end()) mergedAnalysis[x.first] = x.second;
    }
    return mergedAnalysis;
}

bool fixPointReached(BBANALYSIS oldAnalysisMap, BBANALYSIS currentBlockAnalysis) {
    if (oldAnalysisMap.empty() || oldAnalysisMap.size() != currentBlockAnalysis.size()) return false;
    for (auto &it : currentBlockAnalysis) {
        DataInfo obj1 = oldAnalysisMap[it.first];
        DataInfo obj2 = it.second;
        if (obj1.min != obj2.min || obj1.max != obj2.max || obj1.initialized != obj2.initialized) return false;
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
            Instruction* operand = llvm::dyn_cast<Instruction>(I.getOperand(0));
            DataInfo obj = analysis.find(operand)->second;
            analysis[inst] = obj;
        } else if (isa<StoreInst>(I)) {
            Value* v = I.getOperand(0);
            Instruction* source = llvm::dyn_cast<Instruction>(v);
            Instruction* target = llvm::dyn_cast<Instruction>(I.getOperand(1));

            if (isa<ConstantInt>(v)) {
                auto *constant = dyn_cast<ConstantInt>(v);
                int val = constant->getSExtValue();
                DataInfo obj;
                obj.min = val;
                obj.max = val;
                analysis[target] = obj;
            } else {
                DataInfo obj = analysis.find(source)->second;
                analysis[target] = obj;
            }
        } else if (isa<BinaryOperator>(I)) {
            std::string opcode = I.getOpcodeName();
            Instruction* inst = dyn_cast<Instruction>(&I);

            Value* op1 = I.getOperand(0);
            Value* op2 = I.getOperand(1);

            DataInfo value1;
            DataInfo value2;
            int val1, val2;

            if (ConstantInt *CI = dyn_cast<ConstantInt>(op1)) {
                val1 = CI->getSExtValue();
                value1.min = val1;
                value1.max = val1;
                value1.initialized = true;
            } else value1 = analysis.find(dyn_cast<Instruction>(op1))->second;

            if (ConstantInt *CI = dyn_cast<ConstantInt>(op2)){
                val2 = CI->getSExtValue();
                value2.min = val2;
                value2.max = val2;
                value2.initialized = true;
            } else value2 = analysis.find(dyn_cast<Instruction>(op2))->second;

            DataInfo evaluationValue = evaluateOperators(opcode, value1, value2);
            analysis[inst] = evaluationValue;
        }
    }
    return analysis;
}

DataInfo evaluateOperators(std::string opCode, DataInfo obj1, DataInfo obj2) {
    DataInfo obj;

    if (opCode.compare("add") == 0) {
        if(obj1.min == NEG_INFINITY || obj2.min == NEG_INFINITY) obj.min = NEG_INFINITY;
        else obj.min = obj1.min + obj2.min;

        if(obj1.max == POS_INFINITY || obj2.max == POS_INFINITY) obj.max = POS_INFINITY;
        else obj.max = obj1.max + obj2.max;
    } else if (opCode.compare("sub") == 0) {
        obj.min = obj1.min - obj2.min;
        obj.max = obj1.max - obj2.max;
    } else if (opCode.compare("mul") == 0) {
        int o1 = obj1.min * obj2.min;
        int o2 = obj1.max * obj2.max;
        int o3 = obj1.min * obj2.max;
        int o4 = obj1.max * obj2.min;

        int min1 = std::min(o1, o2);
        int min2 = std::min(o3, o4);

        int max1 = std::max(o1, o2);
        int max2 = std::max(o3, o4);

        obj.min = std::min(min1, min2);
        obj.max = std::max(max1, max2);
    } else if (opCode.compare("udiv") == 0 || opCode.compare("sdiv") == 0) {
        if (0 > obj2.min && 0 < obj2.max) {
            obj.min = NEG_INFINITY;
            obj.max = POS_INFINITY;
        } else {
            int o1 = obj1.min / obj2.min;
            int o2 = obj1.max / obj2.max;
            int o3 = obj1.min / obj2.max;
            int o4 = obj1.max / obj2.min;

            int min1 = std::min(o1, o2);
            int min2 = std::min(o3, o4);

            int max1 = std::max(o1, o2);
            int max2 = std::max(o3, o4);

            obj.min = std::min(min1, min2);
            obj.max = std::max(max1, max2);
        }
    } else if (opCode.compare("urem") == 0 || opCode.compare("srem") == 0) {
        obj.min = 0;
        obj.max = obj2.max - 1;
    } else printf("Unsupported operations");
    obj.min = std::min(obj.min, obj.max);
    obj.max = std::max(obj.min, obj.max);
    return obj;
}

std::set<std::pair <std::string,int>> getMaxSeparation(BBANALYSIS bbAnalysis) {
    std::set<std::pair <std::string,int>> maxSet;
    for (auto &x : bbAnalysis) {
        if (isa<AllocaInst>(x.first)) {
            for(auto &y : bbAnalysis) {
                if (isa<AllocaInst>(y.first)) {
                    std::string str1 = getInstructionLabel(x.first);
                    std::string str2 = getInstructionLabel(y.first);
                    DataInfo obj1 = x.second;
                    DataInfo obj2 = y.second;
                    if(str1 != str2 && str1.compare(str2) > 0) {
                        if(obj1.min == NEG_INFINITY || obj1.max == POS_INFINITY || obj2.min == NEG_INFINITY || obj2.max == POS_INFINITY) {
                            std::string str = "[" + str1 + ", " + str2 + "]";
                            maxSet.insert(std::make_pair(str, POS_INFINITY));
                        } else {
                            int diff = std::max(std::abs(obj1.max - obj2.min), std::abs(obj1.min - obj2.max));
                            std::string str = "[" + str1 + ", " + str2 + "]";
                            maxSet.insert(std::make_pair(str, diff));
                        }
                    }
                }
            }
        }
    }
    return maxSet;
}

bool getBranches(BBANALYSIS bbAnalysis, const ICmpInst* I, bool trueBranch) {
    ICmpInst::Predicate predicate = I->getPredicate();

    Value* v1 = I->getOperand(0);
    Value* v2 = I->getOperand(1);
    Instruction* source = llvm::dyn_cast<Instruction>(v1);
    Instruction* target = llvm::dyn_cast<Instruction>(v2);

    DataInfo op1;
    if (isa<ConstantInt>(v1)) {
        auto *constant = dyn_cast<ConstantInt>(v1);
        int val = constant->getSExtValue();
        op1.min = val;
        op1.max = val;
    } else op1 = bbAnalysis.find(source)->second;

    DataInfo op2;
    if (isa<ConstantInt>(v2)) {
        auto *constant = dyn_cast<ConstantInt>(v2);
        int val = constant->getSExtValue();
        op2.min = val;
        op2.max = val;
    } else op2 = bbAnalysis.find(target)->second;

    if(predicate == ICmpInst::ICMP_EQ) {
        if(trueBranch) return (op1.min == op2.min || op1.min == op2.max || op1.max == op2.min || op1.max == op2.max);
        else return !(op1.min == op2.min && op1.min == op2.max && op1.max == op2.min && op1.max == op2.max);
    } else if (predicate == ICmpInst::ICMP_NE) {
        if(trueBranch) return (op1.min != op2.min || op1.min != op2.max || op1.max != op2.min || op1.max != op2.max);
        else return !(op1.min != op2.min && op1.min != op2.max && op1.max != op2.min && op1.max != op2.max);
    } else if (predicate == ICmpInst::ICMP_SGT) {
        if(trueBranch) return (op1.min > op2.min || op1.min > op2.max || op1.max > op2.min || op1.max > op2.max);
        else return !(op1.min > op2.min && op1.min > op2.max && op1.max > op2.min && op1.max > op2.max);
    } else if (predicate == ICmpInst::ICMP_SGE) {
        if(trueBranch) return (op1.min >= op2.min || op1.min >= op2.max || op1.max >= op2.min || op1.max >= op2.max);
        else return !(op1.min >= op2.min && op1.min >= op2.max && op1.max >= op2.min && op1.max >= op2.max);
    } else if (predicate == ICmpInst::ICMP_SLT) {
        if(trueBranch) return (op1.min < op2.min || op1.min < op2.max || op1.max < op2.min || op1.max < op2.max);
        else return (op1.min < op2.min && op1.min < op2.max && op1.max < op2.min && op1.max < op2.max);
    } else if (predicate == ICmpInst::ICMP_SLE) {
        if(trueBranch) return (op1.min <= op2.min || op1.min <= op2.max || op1.max <= op2.min || op1.max <= op2.max);
        else return (op1.min <= op2.min && op1.min <= op2.max && op1.max <= op2.min && op1.max <= op2.max);
    } else return trueBranch;
}

// Printing Basic Block Label
std::string getSimpleNodeLabel(const BasicBlock *Node) {
    if (!Node->getName().empty()) return Node->getName().str();
    std::string Str;
    raw_string_ostream OS(Str);
    Node->printAsOperand(OS, false);
    return OS.str();
}

std::string getInstructionLabel(const Instruction *Node) {
    if (!Node->getName().empty()) return Node->getName().str();
    std::string Str;
    raw_string_ostream OS(Str);
    Node->printAsOperand(OS, false);
    return OS.str();
}

void printAnalysisMap(std::map<std::string, BBANALYSIS> analysisMap) {
    for (auto &row : analysisMap) {
        std::string BBLabel = row.first;
        BBANALYSIS bbAnalysis = row.second;
        outs() << BBLabel << ":\n";

        for (auto &x : bbAnalysis) {
            std::string min = x.second.min == NEG_INFINITY ? "-Infinity": std::to_string(x.second.min);
            std::string max = x.second.max == POS_INFINITY ? "+Infinity": std::to_string(x.second.max);
            std::cout << getInstructionLabel(x.first) << '[' << min << ',' << max << ']' << std::endl;
        }
        outs() << "\n";
    }
}
//include the public part of DSWP
#include "DSWP.h"

using namespace llvm;
using namespace std;



STATISTIC(LoopCounter, "Counts number of loops greeted");

/*QNode::QNode(int u, int latency) {
	this->u = u;
	this->latency = latency;
}

bool QNode::operator < (const QNode &y) const {
	return latency < y.latency;
}

Edge::Edge(Instruction *u, Instruction *v, DType dtype) {
	this->u = u;
	this->v = v;
	this->dtype = dtype;
}*/

char DSWP::ID = 0;
static RegisterPass<DSWP> X("depend", "extract dependency graph", false, true);

DSWP::DSWP() : LoopPass (ID){
	loopCounter = 0;
	errs() << "ENTREING INITIALIAZE\n";
}

bool DSWP::doInitialization(Loop *L, LPPassManager &LPM) {
	errs() << "ENTREING INITIALIAZE\n";
	Module *mod = L->getHeader()->getParent()->getParent();

	Function *produce = mod->getFunction("sync_produce");
	if (produce == NULL) {	//the first time, we need to link them

		LLVMContext &ctx = mod->getContext();
		Type *void_ty = Type::getVoidTy(ctx),
		     *int32_ty = Type::getInt32Ty(ctx),
		     *int64_ty = Type::getInt64Ty(ctx),
		     *int8_ptr_ty = Type::getInt8PtrTy(ctx),
		     *elTy = int64_ty;

		//add sync_produce function
		vector<Type *> produce_arg;
		produce_arg.push_back(elTy);
		produce_arg.push_back(int32_ty);
		FunctionType *produce_ft = FunctionType::get(void_ty, produce_arg, false);
		produce = Function::Create(produce_ft, Function::ExternalLinkage, "sync_produce", mod);
		produce->setCallingConv(CallingConv::C);

		//add syn_consume function
		vector<Type *> consume_arg;
		consume_arg.push_back(int32_ty);
		FunctionType *consume_ft = FunctionType::get(elTy, consume_arg, false);
		Function *consume = Function::Create(consume_ft, Function::ExternalLinkage, "sync_consume", mod);
		consume->setCallingConv(CallingConv::C);

		//add sync_join
		FunctionType *join_ft = FunctionType::get(void_ty, false);
		Function *join = Function::Create(join_ft, Function::ExternalLinkage, "sync_join", mod);
		join->setCallingConv(CallingConv::C);

		//add sync_init
		FunctionType *init_ft = FunctionType::get(void_ty, false);
		Function *init = Function::Create(init_ft, Function::ExternalLinkage, "sync_init", mod);
		init->setCallingConv(CallingConv::C);

		//add sync_delegate
		vector<Type *>  argFunArg;
		argFunArg.push_back(int8_ptr_ty);
		FunctionType *argFun = FunctionType::get(int8_ptr_ty, argFunArg, false);

		vector<Type *> delegate_arg;
		delegate_arg.push_back(int32_ty);
		delegate_arg.push_back(PointerType::get(argFun, 0));
		delegate_arg.push_back(int8_ptr_ty);
		FunctionType *delegate_ft = FunctionType::get(void_ty, delegate_arg, false);
		Function *delegate = Function::Create(delegate_ft, Function::ExternalLinkage, "sync_delegate", mod);
		delegate->setCallingConv(CallingConv::C);

		//add show value
		vector<Type *> show_arg;
		show_arg.push_back(int64_ty);
		FunctionType *show_ft = FunctionType::get(void_ty, show_arg, false);
		Function *show = Function::Create(show_ft, Function::ExternalLinkage, "showValue", mod);
		show->setCallingConv(CallingConv::C);

		//add showPlace value
		vector<Type *> show2_arg;
		FunctionType *show2_ft = FunctionType::get(void_ty, show2_arg, false);
		Function *show2 = Function::Create(show2_ft, Function::ExternalLinkage, "showPlace", mod);
		show2->setCallingConv(CallingConv::C);

		//add showPtr value
		vector<Type *> show3_arg;
		show3_arg.push_back(int8_ptr_ty);
		FunctionType *show3_ft = FunctionType::get(void_ty, show3_arg, false);
		Function *show3 = Function::Create(show3_ft, Function::ExternalLinkage, "showPtr", mod);
		show3->setCallingConv(CallingConv::C);

		return true;
	}
	return false;
}

void DSWP::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<LoopInfo>();
    AU.addPreserved<LoopInfo>();
    AU.addRequiredID(LoopSimplifyID);
    AU.addPreservedID(LoopSimplifyID);
 //AU.addRequired<DominatorTree>();
    AU.addRequired<PostDominatorTree>();
    AU.addRequired<AliasAnalysis>();
    AU.addRequired<MemoryDependenceAnalysis>();
    AU.addRequiredTransitive<PostDominatorTree>();
    AU.addRequired<ScalarEvolution>();
    AU.addPreserved<ScalarEvolution>();

}


bool DSWP::initialize(Loop *L) {
	// loop-level initialization. shouldn't do this in doInitialize because
	// it's not necessarily called immediately before runOnLoop....
	header = L->getHeader();
	func = header->getParent();
	module = func->getParent();
	context = &module->getContext();
	eleType = Type::getInt64Ty(*context);

	predecessor = L->getLoopPredecessor();
	exit = L->getExitBlock();
	loopCounter++;

	if (exit == NULL) {
		cerr << "loop exit not unique" << endl;
		return true;
	} else if (predecessor == NULL) {
		cerr << "loop predecessor not unique" << endl;
		return true;
	}
	return false;
}


bool DSWP::runOnLoop(Loop *L, LPPassManager &LPM) {
	AA = &getAnalysis<AliasAnalysis>();
	AliasA = AA;
	
	std::ofstream outFile;//("operands.txt");
	outFile.open("operands.txt", std::ofstream::app);
	++LoopCounter;

//////////////////////
	ScalarEvolution * SE;
	LoopInfo * LI;
	bool Changed = false;
	if (!L->isLoopSimplifyForm()){
		errs() << "Loop is not in simplified form...\n";
		return false;
	}
	LI = &getAnalysis<LoopInfo>();
	SE = &getAnalysis<ScalarEvolution>();
//	Changed |= OptimizeLoop(L);

//	return Changed;

	unsigned TripCount = 0;
	unsigned TripMultiple = 0;
	unsigned TripExit = 0;

	BasicBlock *ExitingBlock = L->getLoopLatch();
	if (!ExitingBlock || !L->isLoopExiting(ExitingBlock))
		ExitingBlock = L->getExitingBlock();
	if (ExitingBlock) {
		TripCount = SE->getSmallConstantTripCount(L, ExitingBlock);
		//TripMultiple = SE->getSmallConstantTripMultiple(L, ExitingBlock);
		//TripExit = SE->getExitCount(L, ExitingBlock); 	
	}

 //	if (LoopCounter == 1)
PHINode *indv = NULL;
indv = L->getCanonicalInductionVariable();
	Instruction *loopStart = L->getHeader()->begin();
	errs() << "Loop: " << LoopCounter << "  "<< TripCount << '\n';
	  Function *func = loopStart->getParent()->getParent();
	std::string funcName = func->getName().str();
	if (!L->getCanonicalInductionVariable())
		errs() << L->getCanonicalInductionVariable() << "\n";
	else 
		errs() << "No Canonical Loop\n";


	//TODO: here you can add operation printing
/*for (Function::iterator i = func->begin(), e = func->end(); i != e; ++i)
	  // Print out the name of the basic block if it has one, and then the
	  // number of instructions that it contains
	  errs() << "Basic block (name=" << i->getName() << ") has "
		               << i->size() << " instructions.\n";
*/
//////////////////////////////////////////////////
	if (!(std::find(fnameList.begin(), fnameList.end(), func->getName().str()) != fnameList.end())){
		 fnameList.push_back(func->getName().str());
		 outFile << funcName << "\n";
	}
//////////////////////////////// extract opcodes of important instruction in loops
	std::string bbname;
for (Loop::block_iterator bi = L->block_begin(); bi != L->block_end(); bi++) {
		BasicBlock *BB = *bi;

		bool isPresent = 0;
		//outFile <<">>BASIC BLOCK "<<BB->getName().str()<<")\n";
		if (std::find(BBnameList.begin(), BBnameList.end(), BB->getName().str()) != BBnameList.end())
			isPresent = 1;
		//bool isPresent = (std::find(BBnameList.begin(), BBnameList.end(), BB->getName().str()) != BBnameList.end());
		if (!isPresent){
		 	BBnameList.push_back(BB->getName().str());
			outFile << LoopCounter << ": ";
		for (BasicBlock::iterator ui = BB->begin(); ui != BB->end(); ui++) {
			Instruction *inst = &(*ui);
			if (!strcmp(inst->getOpcodeName(), "fmul") )
	   			outFile << inst->getOpcodeName() << " ";
			else if (!strcmp(inst->getOpcodeName(), "fsub") )
	  			outFile << inst->getOpcodeName() << " ";
			else if (!strcmp(inst->getOpcodeName(), "fadd") )
	  			outFile << inst->getOpcodeName() << " ";
			else if (!strcmp(inst->getOpcodeName(), "fdiv") )
	  			outFile << inst->getOpcodeName() << " ";
			else if (!strcmp(inst->getOpcodeName(), "frem") )
	  			outFile << inst->getOpcodeName() << " ";
		  	else if (!strcmp(inst->getOpcodeName(), "fcmp"))
	  			outFile << "fcmp ";
			//integer instructions
			else if (!strcmp(inst->getOpcodeName(), "add"))
	  			outFile << "add ";	
		  	else if (!strcmp(inst->getOpcodeName(), "sub"))
	  			outFile << "sub ";
		  	else if (!strcmp(inst->getOpcodeName(), "mul"))
	  			outFile << "mul ";
		  	else if (!strcmp(inst->getOpcodeName(), "udiv"))
	  			outFile << "udiv ";
		  	else if (!strcmp(inst->getOpcodeName(), "sdiv"))
	  			outFile << "sdiv ";
		  	else if (!strcmp(inst->getOpcodeName(), "urem"))
	  			outFile << "urem ";
		  	else if (!strcmp(inst->getOpcodeName(), "srem"))
	  			outFile << "srem ";
		  	else if (!strcmp(inst->getOpcodeName(), "and"))
	  			outFile << "and ";
		  	else if (!strcmp(inst->getOpcodeName(), "or"))
	  			outFile << "or ";
		  	else if (!strcmp(inst->getOpcodeName(), "xor"))
	  			outFile << "xor ";
		  	//else if (!strcmp(I.getOpcodeName(), "icmp")) //icmp gets an argument declaring whether it is eq, slt, ...
	  		//	outFile << "icmp";
		  	else if (!strcmp(inst->getOpcodeName(), "shl"))
	  			outFile << "shl ";
		  	else if (!strcmp(inst->getOpcodeName(), "lshr"))
	  			outFile << "lshr ";
		  	else if (!strcmp(inst->getOpcodeName(), "ashr"))
	  			outFile << "ashr";
		  	//else if (!strcmp(I.getOpcodeName(), "cmpxchg"))
	  			//outFile << "U";
		  	//else if (!strcmp(I.getOpcodeName(), "shufflevector"))
	  			//outFile << "V";
			//fp operations
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.sqrt") || !strcmp(inst->getOpcodeName(), "sqrt") )
	  			outFile << "sqrt ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.powi") || !strcmp(inst->getOpcodeName(), "powi") )
	  			outFile << "powi ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.sin") || !strcmp(inst->getOpcodeName(), "sin") )
	  			outFile << "sin ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.cos") || !strcmp(inst->getOpcodeName(), "cos") )
	  			outFile << "cos ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.pow") || !strcmp(inst->getOpcodeName(), "pow") )
	  			outFile << "pow ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.exp") || !strcmp(inst->getOpcodeName(), "exp") )
	  			outFile << "exp ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.exp2") || !strcmp(inst->getOpcodeName(), "exp2") )
	  			outFile << "exp2";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.log") || !strcmp(inst->getOpcodeName(), "log") )
	  			outFile << "log ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.log10") || !strcmp(inst->getOpcodeName(), "log10") )
	  			outFile << "log10 ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.log2") || !strcmp(inst->getOpcodeName(), "log2") )
	  			outFile << "log2 ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.fma") || !strcmp(inst->getOpcodeName(), "fma") )
	  			outFile << "fma ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.fabs") || !strcmp(inst->getOpcodeName(), "fabs") )
	  			outFile << "fabs ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.minnum") || !strcmp(inst->getOpcodeName(), "minnum") )
	  			outFile << "minnum ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.maxnum") || !strcmp(inst->getOpcodeName(), "maxnum") )
	  			outFile << "maxnum ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.copysign") || !strcmp(inst->getOpcodeName(), "copysign") )
	  			outFile << "~ ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.floor") || !strcmp(inst->getOpcodeName(), "floor") )
	  			outFile << "floor ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.ceil") || !strcmp(inst->getOpcodeName(), "ceil") )
	  			outFile << "ceil ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.trunc") || !strcmp(inst->getOpcodeName(), "trunc") )
	  			outFile << "trunc ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.rint") || !strcmp(inst->getOpcodeName(), "rint") )
	  			outFile << "rint ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.round") || !strcmp(inst->getOpcodeName(), "round") )
	  			outFile << "round ";
		  	else if (!strcmp(inst->getOpcodeName(), "llvm.nearbyint") || !strcmp(inst->getOpcodeName(), "nearbyint") )
	  			outFile << "nint";
		  	else if (!strcmp(inst->getOpcodeName(), "call") && inst->getNumOperands() == 2 && inst->getOperand(1)->hasName() ){
			  	if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "log")) 
	  				outFile << "log ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "sin")) 
	  				outFile << "sin ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "exp")) 
	  				outFile << "exp ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "abs")) 
	  				outFile << "abs ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "cos")) 
	  				outFile << "cos ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "exp2")) 
	  				outFile << "exp2 ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "sqrt")) 
	  				outFile << "sqrt ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "pow")) 
	  				outFile << "pow ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "log2")) 
	  				outFile << "log2 ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "log10")) 
	  				outFile << "log10 ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "fabs")) 
	  				outFile << "fabs ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "floor")) 
	  				outFile << "floor ";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "ceil")) 
	  				outFile << "ceil";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "fmuladd")) 
	  				outFile << "fmuladd";
			  	else if (!strcmp(inst->getOperand(1)->getName().str().c_str(), "fma")) 
	  				outFile << "fma";

		}
		}
			outFile << "\n";	
		}
		//else outFile << "bb was there before\n";
}
outFile << "\n";

/////////////////////////

	//TODO atie: getSubLoops
	/*	if (L->getLoopDepth() != 1){	//ONLY care about top level loops
		errs() << "Not a top level loop!\n";
    		return false;
	}*/

//	if (generated.find(L->getHeader()->getParent()) != generated.end())	//this is the generated code
//		return false;
	
//	CountValue *TripCount = getTripCount(L);

//	Function *func = loopStart->getParent()->getParent();

	errs()  << "func name: " << funcName << "\n";
    for (Function::iterator b = func->begin(), be = func->end(); b != be; b++) {
        for (BasicBlock::iterator instr = b->begin(), ie = b->end();
             instr != ie; ++instr) {

    	     //InstructionNode *iNode = new InstructionNode(instr);
            updateDAGwithInst(instr);
        }
    }

    for (Function::iterator b = func->begin(), be = func->end(); b != be; b++) {
        for (BasicBlock::iterator instr = b->begin(), ie = b->end();
             instr != ie; ++instr) {
            generateDependencies(instr);
	    //errs() << "instr: "; instr->dump();
        }
    }

/////////////////////////////////////////////////////////
for (Loop::block_iterator bi = L->block_begin(); bi != L->block_end(); bi++) {
		BasicBlock *BB = *bi;
	//	errs()<<">>BASIC BLOCK ("<<BB->getName().str()<<")\n";

		for (BasicBlock::iterator ui = BB->begin(); ui != BB->end(); ui++) {
			Instruction *inst = &(*ui);
	    	//errs()  <<  "Opcode : "<<  inst->getOpcodeName() << "\n";
	//		errs() << "Inst: ";
	//		inst->dump();
			InstructionNode *inNode = getInstructionNode(inst);
	  		for (InstructionNode::iterator i = inNode->dep_begin(), e = inNode->dep_end(); i!= e; ++i) {
				InstructionNode *depIn = *i;
	//			errs() << "has reg dependency from ";
	//			depIn->getInst()->dump();
			}
/*	  		for (InstructionNode::iterator mi = inNode->mem_dep_begin(), me = inNode->mem_dep_end(); mi!= me; ++mi) {
				InstructionNode *depIn = *mi;
				errs() << "has mem dependency from ";
				depIn->getInst()->dump();
			}*/

			for (InstructionNode::iterator si = inNode->use_begin(), send = inNode->use_end(); si != send; ++si) {
			        InstructionNode *succ = *si;
	//			errs() << "its succesor is ";
	//			succ->getInst()->dump();
			}
			for (InstructionNode::iterator msi = inNode->mem_use_begin(), msend = inNode->mem_use_end(); msi != msend; ++msi) {
			        InstructionNode *succ = *msi;
	//			errs() << "its mem succesor is ";
	//			succ->getInst()->dump();
			}



	}
}
//InstructionNode *depNode = getInstructionNode(dep);
//        iNode->addDepInst(depNode);
//        depNode->addUseInst(iNode);
/*
for (Loop::block_iterator bi = L->block_begin(); bi != L->block_end(); bi++) {
		BasicBlock *BB = *bi;
		errs()<<">>BASIC BLOCK ("<<BB->getName().str()<<")\n";


    //bool ignoreDummyCalls = !LEGUP_CONFIG->getParameterInt("DFG_SHOW_DUMMY_CALLS");
    for (BasicBlock::iterator I = BB->begin(), ie = BB->end(); I != ie; ++I) {
        InstructionNode *op = getInstructionNode(I);
        //if (ignoreDummyCalls && isaDummyCall(I))
        if (isaDummyCall(I))
            continue;
	errs() << "for Instr: ";
	I->dump();
	errs() << " Uses are: ";
//        std::string label = "label=\"D:" + ftostr(op->getDelay()) + "ns L:" +                            utostr(Scheduler::getNumInstructionCycles(I)) + "\",";
        for (Value::use_iterator use = I->use_begin(), e = I->use_end(); use != e; ++use) {
            if (Instruction *child = dyn_cast<Instruction>(*use)) {
               // if (ignoreDummyCalls && isaDummyCall(child))
               if (isaDummyCall(child))
                    continue;
                //graph.connectDot(out, op, getInstructionNode(child), label + "color=blue");
                child->dump();
            }
        }

        for (InstructionNode::iterator use = op->mem_use_begin(), e = op->mem_use_end(); use != e; ++use) {
          //  if (ignoreDummyCalls && isaDummyCall((*use)->getInst()))
            if (isaDummyCall((*use)->getInst()))
                continue;
            //graph.connectDot(out, op, *use, label + "color=red");
	    (*use)->getInst()->dump();
        }
    }
}
*/


///////////////////////////////////////////////////////////

	
//	errs() << "Entering loop "  << L->getHeader()->getName() << "  " << LoopCounter << " in function " << funcName << "\n";

/*	bool bad = initialize(L);
	if (bad) {
		clear();
		return false;
	}

	buildPDG(L);*/
	outFile.close();
	return true;
}
////////////////////////////
/*CountValue *DSWP::getTripCount(MachineLoop *L) const {
	  const MachineInstr *IV_Inst = getCanonicalInductionVariable(L);
	    if (IV_Inst == 0) 
		    return 0;
	    const MachineOperand *IV_Opnd;
	    const MachineOperand *InitialValue;
	    if (!L->contains(IV_Inst->getOperand(2).getMBB())) {
		    InitialValue = &IV_Inst->getOperand(1);
		    IV_Opnd = &IV_Inst->getOperand(3);
	    } else {
		    InitialValue = &IV_Inst->getOperand(3);
		    IV_Opnd = &IV_Inst->getOperand(1);
	    }
	    while ((IV_Opnd = IV_Opnd->getNextOperandForReg())) {
		    const MachineInstr *MI = IV_Opnd->getParent();
		    if (L->contains(MI) && isCompareEqualsImm(MI)) {
			    const MachineOperand &MO = MI->getOperand(2);
			    assert(MO.isImm() && "IV Cmp Operand should be 0");
			    int64_t ImmVal = MO.getImm();
			    const MachineInstr *IV_DefInstr = MRI->getVRegDef(IV_Opnd->getReg());
			    assert(L->contains(IV_DefInstr->getParent()) && "IV definition should occurs in loop");
			    int64_t iv_value = IV_DefInstr->getOperand(2).getImm();
			    if (ImmVal == 0) {
				    if (iv_value != 1 && iv_value != -1) {
					    return 0;
				    }
				    return new CountValue(InitialValue->getReg(), iv_value > 0);
			    } else {
				    assert(InitialValue->isReg() && "Expecting register for init value");
				    const MachineInstr *DefInstr = MRI->getVRegDef(InitialValue->getReg());
				    if (DefInstr && DefInstr->getOpcode() == Hexagon::TFRI) {
					    int64_t count = ImmVal - DefInstr->getOperand(1).getImm();
					    if ((count % iv_value) != 0) {
						    return 0;
					    }
					    return new CountValue(count/iv_value);																			          }
										
			    }
		    }
	    }
	    return 0;
}
*/

//////////////////////////////////
void DSWP::addEdge(Instruction *u, Instruction *v, DType dtype) {
	if (std::find(pdg[u].begin(), pdg[u].end(), Edge(u, v, dtype)) ==
				pdg[u].end()) {
		pdg[u].push_back(Edge(u, v, dtype));
		allEdges.push_back(Edge(u, v, dtype));
		rev[v].push_back(Edge(v, u, dtype));
	}
	else
		cout<<">>Skipping the edge, as it has been added already."<<endl;
}

bool DSWP::checkEdge(Instruction *u, Instruction *v) {

	for (vector<Edge>::iterator it = pdg[u].begin(); it != pdg[v].end(); it++) {
		if (it->v == v) {
			//TODO report something
			return true;
		}
	}
	return false;
}


void DSWP::dfsVisit(BasicBlock *BB, std::set<BasicBlock *> &vis,
					std::vector<BasicBlock *> &ord, Loop *L) {
	vis.insert(BB); //Mark as visited
	for (succ_iterator SI = succ_begin(BB), E = succ_end(BB); SI != E; ++SI)
		if (L->contains(*SI) && vis.find(*SI) == vis.end())
			dfsVisit(*SI, vis, ord, L);

	ord.push_back(BB);
}

void DSWP::updateDAGwithInst(Instruction *instr) {
    // generate Instruction to InstructionNode mapping
    InstructionNode *iNode = new InstructionNode(instr);
    nodeLookup[instr] = iNode;
}


void DSWP::generateDependencies(Instruction *instr) {
    InstructionNode *iNode = getInstructionNode(instr);
    //instr->dump();
    // generate dependencies
    regDataDeps(iNode);

    if (isa<LoadInst>(*instr) || isa<StoreInst>(*instr)) {
//        if (LEGUP_CONFIG->getParameterInt("ALIAS_ANALYSIS")) {
            memDataDeps(iNode); // create dependencies based on LLVM alias analysis
//        } else {
          //  callDataDeps(iNode); // create dependences in same order as in IR
                                 // [LegUp 1.0 & 2.0 functionality]
        }
/*    } else if (isa<CallInst>(instr)) {
        callDataDeps(iNode);
    }*/
}

// Add dependencies for all the operands of iNode
// ie. %3 = add %1, %2
// %3 is dependent on %1 and %2
// %1 is used by %3
// %2 is used by %3
void DSWP::regDataDeps(InstructionNode *iNode) {
    Instruction *inst = iNode->getInst();
    // these instructions are not scheduled
    if (isa<AllocaInst>(inst) || isa<PHINode>(inst))
        return;
//    errs() << "reg data deps for ";
//    inst.dump();
    for (User::op_iterator i = inst->op_begin(), e = inst->op_end(); i != e;
         ++i) {
        // we only care about operands that are created by other instructions
        Instruction *dep = dyn_cast<Instruction>(*i);
        // also ignore if the dependency is an alloca
        if (!dep || isa<AllocaInst>(dep))
            continue;

        // ignore operands from other basic blocks, these are
        // guaranteed to be in another state
        if (dep->getParent() != inst->getParent())
            continue;

        InstructionNode *depNode = getInstructionNode(dep);
        iNode->addDepInst(depNode);
        depNode->addUseInst(iNode);
    }
}

// find all memory dependencies: I1 -> I2 (where I2 is given)
void DSWP::memDataDeps(InstructionNode *I2Node) {
    Instruction *I2 = I2Node->getInst();
//    errs() << "In MemDataDeps ... \n";
  //  I2->dump();
    BasicBlock *bb = I2->getParent();

    // loop over all candidates for I1 in the BB for dependencies I1 -> I2
    for (BasicBlock::iterator dep = bb->begin(), ie = bb->end(); dep != ie;
         ++dep) {
        Instruction *I1 = dep;

        // If we reach I2 then there are no more candidates for I1
        if (I1 == I2)
            break;

        if (!isa<LoadInst>(I1) && !isa<StoreInst>(I1) && !isa<CallInst>(I1))
            continue;

        if (isaDummyCall(I1))
            continue;

        if (hasDependencyAA(I1, I2)) {
            // errs() << "memDataDeps: I1 -> I2\n" <<
            //    "I1: " << *I1 << "\n" <<
            //    "I2: " << *I2 << "\n";
            InstructionNode *I1Node = getInstructionNode(I1);
            I2Node->addMemDepInst(I1Node);
            I1Node->addMemUseInst(I2Node);
        }
    }
}

bool DSWP::hasDependencyAA(Instruction *I1, Instruction *I2) {
    AliasAnalysis::Location Loc1, Loc2;

    if (isa<CallInst>(I1)) {
        // assume that any loads/stores after a call must indeed execute
        // AFTER the call
        return true;
    }

    // bool store = false;
    if (LoadInst *lInst = dyn_cast<LoadInst>(I1)) {
        Loc1 = AliasA->getLocation(lInst);
    } else if (StoreInst *sInst = dyn_cast<StoreInst>(I1)) {
        Loc1 = AliasA->getLocation(sInst);
        // store = true;
    } else {
        assert(0 && "Unexpected input");
    }

    if (isa<StoreInst>(I1) && isa<LoadInst>(I2)) {
        // RAW dependency:
        // I1 is a store and I2 is a load from potentially the same address
        LoadInst *lInst = dyn_cast<LoadInst>(I2);
        Loc2 = AliasA->getLocation(lInst);
        if (!AliasA->isNoAlias(Loc1, Loc2)) {
		for (int j = 0; j < I1->getNumOperands(); j++){
			for (int k = 0; k < I2->getNumOperands(); k++){
				if (I1->getOperand(j)->getName() == I2->getOperand(k)->getName())
            				return true;
			}
		}
        }

    } else if (isa<StoreInst>(I2)) {
        // WAW or WAR dependency:
        // I1 is a store OR a load and I2 is a store to
        // potentially same address
        StoreInst *sInst = dyn_cast<StoreInst>(I2);
        Loc2 = AliasA->getLocation(sInst);
        if (!AliasA->isNoAlias(Loc1, Loc2)) {
		for (int j = 0; j < I1->getNumOperands(); j++){
			for (int k = 0; k < I2->getNumOperands(); k++){
				if (I1->getOperand(j)->getName() == I2->getOperand(k)->getName())
            				return true;
			}
		}


      //      return true;
        }
    } else {
        // RAR: no dependency
        assert(isa<LoadInst>(I1) && isa<LoadInst>(I2));
    }

    return false;
}



// find all memory dependencies: I1 -> I2 (where I2 is given)
void DSWP::callDataDeps(InstructionNode *I2Node) {
    Instruction *I2 = I2Node->getInst();
    BasicBlock *b = I2->getParent();

    if (isaDummyCall(I2) && !isaPrintCall(I2))
        return;

    // loop over all candidates for I1 in the BB for dependencies I1 -> I2
    for (BasicBlock::iterator dep = b->begin(), ie = b->end(); dep != ie;
         ++dep) {
        Instruction *I1 = dep;

        // If we reach I2 then there are no more candidates for I1
        if (I1 == I2)
            break;

        if (!isa<LoadInst>(I1) && !isa<StoreInst>(I1) && !isa<CallInst>(I1))
            continue;

        if (isaDummyCall(I1) && !isaPrintCall(I1))
            continue;

        InstructionNode *I1Node = getInstructionNode(I1);
        I2Node->addMemDepInst(I1Node);
        I1Node->addMemUseInst(I2Node);
    }
}


bool DSWP::isaDummyCall(const Instruction *instr) {
    const CallInst *ci = dyn_cast<CallInst>(instr);
    if (!ci) {
        return false;
    }

    Function *calledFunc = ci->getCalledFunction();
    // ignore indirect function invocations
    if (!calledFunc) {
        return false;
    }

/*    //if it's an openmp function call
    //ignore all call instructions except for the first one with a threadID of 0
    int parallelInstances = getMetadataInt(instr, "NUMTHREADS");
    std::string functionType = getMetadataStr(instr, "TYPE");
	if (parallelInstances != 0 && functionType == "omp_function") {
        int threadID = getMetadataInt(instr, "THREADID");
        if (threadID != 0) {
            //errs () << "this is a dummy parallel function!\n";
            return true;
        }
    }*/

    std::string funcName = calledFunc->getName();
    return (funcName == "printf" 
	    || funcName == "puts" 
	    || funcName == "putchar"
            || funcName == "exit"
            || funcName == "llvm.lifetime.start"
            || funcName == "llvm.lifetime.end"
            || funcName == "llvm.invariant.start"
            || funcName == "llvm.invariant.end"
            || funcName == "llvm.dbg.declare"//NC changes
            || funcName == "llvm.dbg.value"//NC changes
           );

}

bool DSWP::isaPrintCall(Instruction *I) {
    const CallInst *ci = dyn_cast<CallInst>(I);
    if (!ci) {
        return false;
    }

    Function *calledFunc = ci->getCalledFunction();
    // ignore indirect function invocations
    if (!calledFunc) {
        return false;
    }
    return (calledFunc->getName() == "printf" || calledFunc->getName() == "puts" ||
            calledFunc->getName() == "putchar");

}


void DSWP::buildPDG(Loop *L) {
	errs()<<">>Building PDG for new loop\n";
}

//===- Disassembler.cpp - Disassembler for hex strings --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This class implements the disassembler of strings of bytes written in
// hexadecimal, from standard input or from a file.
//
//===----------------------------------------------------------------------===//
#include "Disassembler.h"
#include "llvm/ADT/Triple.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Instruction.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCDisassembler/MCDisassembler.h"
#include "llvm/MC/MCInst.h"
#include "llvm/MC/MCInstPrinter.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCStreamer.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/raw_ostream.h"
#define Window 10 //use window size as bucket
using namespace llvm;

//command line arguments used
static cl::opt<unsigned>
WindowSize(cl::Positional, cl::desc(" Window sized opcode counter"), cl::init(1));

static cl::opt<bool>
EnableOpcodeCount(cl::Positional, cl::desc(" Determines whether or not Opcode counter should be executed"), cl::init(true));


//node structure for hash table
struct node{
 std::vector<unsigned> Opcode; 
 std::vector<std::string> Name;
 int count;
 node *next;
 node()
 {
   Opcode.resize(WindowSize.getValue());
   Name.resize(WindowSize.getValue());
 }
};
typedef struct node *Node;

class HashTable{
 Node table[50];
 public :
  int Hash(std::vector<unsigned>);
  void Insert(std::vector<unsigned>, std::vector<std::string>);
  void Display();
  HashTable(){
    int i;
    //initialise each bucket to NULL
    for(i=0; i<50; i++)
     table[i] = NULL;
  }
};

//hash function
int HashTable::Hash(std::vector<unsigned> Op){
 int result=0,sumcount,prodsum;
 std::vector<int> count, sum;
 unsigned j;
 std::vector<unsigned> newOp;
 count.resize(WindowSize.getValue());
 sum.resize(WindowSize.getValue());
 newOp.resize(WindowSize.getValue());
 for(j=0; j<WindowSize.getValue(); j++){
  count[j]=0;
  sum[j] = 0;
  newOp[j] = Op[j];
  while(newOp[j]!=0){
   sum[j] += newOp[j]%10;
   newOp[j]/=10;
   count[j]++;
  }
 }
 sumcount = 0;
 prodsum = 1;
 for(j=0; j<WindowSize.getValue(); j++){
  sumcount += count[j];
  prodsum *= sum[j];
 }
 result = prodsum + sumcount;
 
 result %= 47;
 result += 3;
 return result;//returns index
}

void HashTable::Insert(std::vector<unsigned> op, std::vector<std::string> opnames){
 Node newnode = new node;
 Node top;
 unsigned index, i, flag = 1;
 index = Hash(op);
 //if node is NULL -> indicates empty list
 if(table[index] == NULL){
  //add newnode and copy all opcodes to it
  table[index] = newnode;
  newnode->next = NULL;
  newnode->count = 1;
  for(i=0; i<WindowSize.getValue(); i++)
  {
   newnode->Opcode[i] = op[i];
   newnode->Name[i] = opnames[i];
  }
  return;
 }
 else
 {
  //if node contains certain other opcode values
  Node prev;
  top = table[index];
  while(top != NULL){
   //if current opcodes are found
   flag = 1;
   prev = top;
   for(i=0; i<WindowSize.getValue(); i++){
    if(top->Opcode[i] != op[i]){
     flag = 0;
     break;
    }
   }
   if(flag){
    top->count++; //increment counter
    return;
   }
   top = top->next; //if current opcodes are not found, check in next element
  }
  //if opcodes do not exist in entire list, add new node to end of list
  prev->next = newnode;
  newnode->next = NULL;
  newnode->count = 1;
  for(i=0; i<WindowSize.getValue() ; i++)
  {
    newnode->Opcode[i] = op[i];
    newnode->Name[i] = opnames[i];
  }
  return;
 }
}

//display element in each node of the hash table if it is not NULL
void HashTable::Display(){
 unsigned  i,j, newcount=0, total=0;
 Node top;
// clrscr();
 for(i=0; i<50; i++){
  top = table[i];
  while(top!=NULL){
   newcount++;
   total+=top->count;
   errs()<<"\nNumber of occurences of ";
   for(j=0; j<WindowSize.getValue() ; j++){
   //avoid extra comma during printing
    if(j==WindowSize.getValue()-1)
     errs()<<top->Name[j];
    else
     errs()<<top->Name[j]<<", ";
  }
   errs()<<" is : "<<top->count;
   top = top->next;
  }
 }
 errs()<<"\nNumber of unique opcode pairs is "<<newcount<<"\n";
}
//mycode ends

typedef std::pair<std::vector<unsigned char>, std::vector<const char *>>
    ByteArrayTy;

static bool PrintInsts(const MCDisassembler &DisAsm,
                       const ByteArrayTy &Bytes,
                       SourceMgr &SM, raw_ostream &Out,
                       MCStreamer &Streamer, bool InAtomicBlock,
                       const MCSubtargetInfo &STI, const std::string &triplename, const Target &T) {
  ArrayRef<uint8_t> Data(Bytes.first.data(), Bytes.first.size());

  // Disassemble it to strings.
  uint64_t Size;
  uint64_t Index;

  if(EnableOpcodeCount.getValue() == false && WindowSize.getValue() > 1)
  {
   errs()<<" Window Size used as 1. ";
   WindowSize = 1;
  }

  
   std::vector<unsigned> op;
   std::vector<std::string> opcodeName;
   op.resize(WindowSize.getValue());
   opcodeName.resize(WindowSize.getValue());

   HashTable t;
   unsigned cflag = 0, i; //cflag is the flag variable used to check the number of entries in op[] array
   for(i=0 ; i<WindowSize.getValue() ; i++)
     op[i] = 0;
  
   for (Index = 0; Index < Bytes.first.size(); Index += Size) {
    MCInst Inst;
   
//if maximum opcodes are entered, then insert the opcodes 
      if(cflag == WindowSize.getValue())
      {
      	t.Insert(op, opcodeName);
	//get next three opcodes
	cflag = WindowSize.getValue()-1;
	for(i=0; i<WindowSize.getValue()-1; i++)
	{
		opcodeName[i] = opcodeName[i+1];
		op[i] = op[i+1];
	}
	op[WindowSize.getValue()-1]=0; 
	opcodeName[WindowSize.getValue()-1] = "\0";
      }
   

    MCDisassembler::DecodeStatus S;
    S = DisAsm.getInstruction(Inst, Size, Data.slice(Index), Index,
                              /*REMOVE*/ nulls(), nulls());
    switch (S) {
    case MCDisassembler::Fail:
      SM.PrintMessage(SMLoc::getFromPointer(Bytes.second[Index]),
                      SourceMgr::DK_Warning,
                      "invalid instruction encoding");
      // Don't try to resynchronise the stream in a block
      if (InAtomicBlock)
        return true;

      if (Size == 0)
        Size = 1; // skip illegible bytes

      break;

    case MCDisassembler::SoftFail:
      SM.PrintMessage(SMLoc::getFromPointer(Bytes.second[Index]),
                      SourceMgr::DK_Warning,
                      "potentially undefined instruction encoding");
      LLVM_FALLTHROUGH;

    case MCDisassembler::Success:
      Streamer.EmitInstruction(Inst, STI);
      if(EnableOpcodeCount.getValue() == true)
      {
	auto const MRI = T.createMCRegInfo(triplename);
	if (!MRI) {
   	 errs() << "error: no register info for target " << triplename << "\n";
   	 return -1;
 	}

	auto const MAI = T.createMCAsmInfo(*MRI, triplename);
	if (!MAI) {
	 errs() << "error: no assembly info for target " << triplename << "\n";
	 return -1;
	}

	//const MCInstrInfo MII(T.createMCInstrInfo());
	auto const MII = T.createMCInstrInfo();
	if(!MII) {
	 errs()<< "error: no instruction info for targe " << triplename << "\n";
	 return -1;
	}
	Triple TheTriple(triplename);
	unsigned int AsmPrinterVariant = MAI->getAssemblerDialect();
	auto myinst= T.createMCInstPrinter(TheTriple, AsmPrinterVariant, *MAI,*MII,*MRI);
	StringRef mystring;
	mystring = myinst->getOpcodeName(Inst.getOpcode());
	opcodeName[cflag] = mystring.str();
        op[cflag++]=Inst.getOpcode(); //add opcodes to the op[] array
      }
      break;
    }
  }
  if(EnableOpcodeCount.getValue() == true)
  {
    t.Insert(op, opcodeName); //to insert the last pair
    t.Display();
  }
  return false;
}

static bool SkipToToken(StringRef &Str) {
  for (;;) {
    if (Str.empty())
      return false;

    // Strip horizontal whitespace and commas.
    if (size_t Pos = Str.find_first_not_of(" \t\r\n,")) {
      Str = Str.substr(Pos);
      continue;
    }

    // If this is the start of a comment, remove the rest of the line.
    if (Str[0] == '#') {
        Str = Str.substr(Str.find_first_of('\n'));
      continue;
    }
    return true;
  }
}


static bool ByteArrayFromString(ByteArrayTy &ByteArray,
                                StringRef &Str,
                                SourceMgr &SM) {
  while (SkipToToken(Str)) {
    // Handled by higher level
    if (Str[0] == '[' || Str[0] == ']')
      return false;

    // Get the current token.
    size_t Next = Str.find_first_of(" \t\n\r,#[]");
    StringRef Value = Str.substr(0, Next);

    // Convert to a byte and add to the byte vector.
    unsigned ByteVal;
    if (Value.getAsInteger(0, ByteVal) || ByteVal > 255) {
      // If we have an error, print it and skip to the end of line.
      SM.PrintMessage(SMLoc::getFromPointer(Value.data()), SourceMgr::DK_Error,
                      "invalid input token");
      Str = Str.substr(Str.find('\n'));
      ByteArray.first.clear();
      ByteArray.second.clear();
      continue;
    }

    ByteArray.first.push_back(ByteVal);
    ByteArray.second.push_back(Value.data());
    Str = Str.substr(Next);
  }

  return false;
}

int Disassembler::disassemble(const Target &T,
                              const std::string &Triple,
                              MCSubtargetInfo &STI,
                              MCStreamer &Streamer,
                              MemoryBuffer &Buffer,
                              SourceMgr &SM,
                              raw_ostream &Out) {

  std::unique_ptr<const MCRegisterInfo> MRI(T.createMCRegInfo(Triple));
  if (!MRI) {
    errs() << "error: no register info for target " << Triple << "\n";
    return -1;
  }

  std::unique_ptr<const MCAsmInfo> MAI(T.createMCAsmInfo(*MRI, Triple));
  if (!MAI) {
    errs() << "error: no assembly info for target " << Triple << "\n";
    return -1;
  }

  // Set up the MCContext for creating symbols and MCExpr's.
  MCContext Ctx(MAI.get(), MRI.get(), nullptr);

  std::unique_ptr<const MCDisassembler> DisAsm(
    T.createMCDisassembler(STI, Ctx));
  if (!DisAsm) {
    errs() << "error: no disassembler for target " << Triple << "\n";
    return -1;
  }

  // Set up initial section manually here
  Streamer.InitSections(false);

  bool ErrorOccurred = false;

  // Convert the input to a vector for disassembly.
  ByteArrayTy ByteArray;
  StringRef Str = Buffer.getBuffer();
  bool InAtomicBlock = false;

  while (SkipToToken(Str)) {
    ByteArray.first.clear();
    ByteArray.second.clear();

    if (Str[0] == '[') {
      if (InAtomicBlock) {
        SM.PrintMessage(SMLoc::getFromPointer(Str.data()), SourceMgr::DK_Error,
                        "nested atomic blocks make no sense");
        ErrorOccurred = true;
      }
      InAtomicBlock = true;
      Str = Str.drop_front();
      continue;
    } else if (Str[0] == ']') {
      if (!InAtomicBlock) {
        SM.PrintMessage(SMLoc::getFromPointer(Str.data()), SourceMgr::DK_Error,
                        "attempt to close atomic block without opening");
        ErrorOccurred = true;
      }
      InAtomicBlock = false;
      Str = Str.drop_front();
      continue;
    }

    // It's a real token, get the bytes and emit them
    ErrorOccurred |= ByteArrayFromString(ByteArray, Str, SM);

    if (!ByteArray.first.empty())
      ErrorOccurred |= PrintInsts(*DisAsm, ByteArray, SM, Out, Streamer,
                                  InAtomicBlock, STI, Triple, T);
  }

  if (InAtomicBlock) {
    SM.PrintMessage(SMLoc::getFromPointer(Str.data()), SourceMgr::DK_Error,
                    "unclosed atomic block");
    ErrorOccurred = true;
  }

  return ErrorOccurred;
}

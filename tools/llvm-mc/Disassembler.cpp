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
#define WindowSize 2 //use window size as bucket
using namespace llvm;

//node structure for hash table
struct node{
 unsigned Opcode[WindowSize]; 
 std::string Name[WindowSize];
 int count;
 node *next;
};
typedef struct node *Node;

class HashTable{
 Node table[50];
 public :
  int Hash(unsigned[]);
  void Insert(unsigned[], std::string[]);
  void Display();
  HashTable(){
    int i;
    //initialise each bucket to NULL
    for(i=0; i<50; i++)
     table[i] = NULL;
  }
};

//hash function
int HashTable::Hash(unsigned Op[]){
 float sum[WindowSize], result=0,sumcount,prodsum, count[WindowSize];
 int res,j;
 unsigned newOp[WindowSize];
 for(j=0; j<WindowSize; j++){
  count[j]=0;
  newOp[j] = Op[j];
  while(newOp[j]!=0){
   sum[j] = newOp[j]%10;
   newOp[j]/=10;
   count[j]++;
  }
 }
 sumcount = 0;
 prodsum = 1;
 for(j=0; j<WindowSize ; j++){
  sumcount += count[j];
  prodsum *= sum[j];
 }
 res = prodsum/sumcount;
 res = floor(result);
 res %= 50;
 return res;//returns index
}

void HashTable::Insert(unsigned op[], std::string opnames[]){
 Node newnode = new node;
 Node top;
 int index, i, flag = 1;
 index = Hash(op);
 //if node is NULL -> indicates empty list
 if(table[index] == NULL){
  //add newnode and copy all opcodes to it
  table[index] = newnode;
  newnode->next = NULL;
  newnode->count = 1;
  for(i=0; i<WindowSize ; i++)
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
   for(i=0; i<WindowSize; i++){
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
  for(i=0; i<WindowSize ; i++)
  {
    newnode->Opcode[i] = op[i];
    newnode->Name[i] = opnames[i];
  }
  return;
 }
}

//display element in each node of the hash table if it is not NULL
void HashTable::Display(){
 int  i, newcount=0, total=0;
 Node top;
 for(i=0; i<50; i++){
  top = table[i];
  while(top!=NULL){
   newcount++;
   total+=top->count;
   errs()<<"\nNumber of occurences of ";
   for(i=0; i<WindowSize ; i++){
    //avoid extra comma during printing
    if(i==WindowSize-1)
     errs()<<top->Name[i];
    else
     errs()<<top->Name[i]<<", ";
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

  unsigned op[WindowSize];
  std::string opcodeName[WindowSize];
  HashTable t;
  int cflag = 0, i; //cflag is the flag variable used to check the number of entries in op[] array
  for(i=0 ; i<WindowSize ; i++)
	op[i] = 0;

  for (Index = 0; Index < Bytes.first.size(); Index += Size) {
    MCInst Inst;

//if maximum opcodes are entered, then insert the opcodes 
    if(cflag == WindowSize)
    {
	t.Insert(op, opcodeName);
	//get next three opcodes
	cflag = WindowSize-1;
	for(i=0; i<WindowSize-1; i++)
	{
		opcodeName[i] = opcodeName[i+1];
		op[i] = op[i+1];
	}
	op[WindowSize-1]=0; 
	opcodeName[WindowSize-1] = "\0";
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
      break;
    }
  }
  t.Insert(op, opcodeName); //to insert the last pair
  t.Display();
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

-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.RamBridge.uniform_bit_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:40:02.959461+00:00
-- url     : https://prove2.me/submissions/5ae95a82-8f56-4314-95f7-5dc138039ddb

import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.IntervalCases
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces
import Theorems.Thm_Lax759944Proofs_TapeRamGenericTime_genericTime_of_lowering_finite_explicit

section

namespace Lax759944Proofs.Encoding

open Lax759944.BinaryWordEncoding

@[simp] theorem encode_nil:encode []=[]:=rfl

@[simp] theorem encode_cons (a:ℕ) (x:List ℕ):
    encode (a::x)=encodeNat a ++ encode x:=rfl

@[simp] theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_cons (a:ℕ) (x:List ℕ):
    bitSize (a::x)=(Nat.bits a).length + 1 + bitSize x:=by
  simp [bitSize,encode,encodeNat,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem length_le_bitSize (x:List ℕ):x.length≤ bitSize x:=by
  induction x with
  | nil => simp
  | cons a x ih =>
      rw [bitSize_cons]
      simp only [List.length_cons]
      omega

end Lax759944Proofs.Encoding

end

section

namespace Lax759944Proofs.Microcode

structure State where

  pc:ℕ

  acc:ℕ

  mem:ℕ→ ℕ

  inp:List ℕ

  out:List ℕ

def setCell (w:ℕ) (m:ℕ→ ℕ) (a v:ℕ):ℕ→ ℕ:=
  fun b => if b=a % 2 ^ w then v % 2 ^ w else m b

def Instr.effect (w:ℕ):Instr→ State→ Option State
  | read a,s =>
      s.inp.head?.map fun v =>
        { s with pc:=s.pc + 1,mem:=setCell w s.mem a v,inp:=s.inp.tail }
  | write o,s =>
      some { s with pc:=s.pc + 1,out:=s.out ++ [o.value w s.mem % 2 ^ w] }
  | load o,s => some { s with pc:=s.pc + 1,acc:=o.value w s.mem % 2 ^ w }
  | store a,s => some { s with pc:=s.pc + 1,mem:=setCell w s.mem a s.acc }
  | storeInd a,s =>
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem (s.mem (a % 2 ^ w)) s.acc }
  | add o,s => some { s with pc:=s.pc + 1,acc:=(s.acc + o.value w s.mem) % 2 ^ w }
  | sub o,s => some { s with pc:=s.pc + 1,acc:=(s.acc - o.value w s.mem) % 2 ^ w }
  | mul o,s => some { s with pc:=s.pc + 1,acc:=(s.acc * o.value w s.mem) % 2 ^ w }
  | div o,s => some { s with pc:=s.pc + 1,acc:=(s.acc / o.value w s.mem) % 2 ^ w }
  | and o,s => some { s with pc:=s.pc + 1,acc:=Nat.land s.acc (o.value w s.mem) % 2 ^ w }
  | or o,s => some { s with pc:=s.pc + 1,acc:=Nat.lor s.acc (o.value w s.mem) % 2 ^ w }
  | xor o,s => some { s with pc:=s.pc + 1,acc:=Nat.xor s.acc (o.value w s.mem) % 2 ^ w }
  | compl _,s =>
      some { s with pc:=s.pc + 1,acc:=(2 ^ w - 1 - s.acc % 2 ^ w) % 2 ^ w }
  | shiftl o,s =>
      some { s with pc:=s.pc + 1,acc:=s.acc * 2 ^ o.value w s.mem % 2 ^ w }
  | shiftr o,s =>
      some { s with pc:=s.pc + 1,acc:=s.acc / 2 ^ o.value w s.mem % 2 ^ w }
  | jump l,s => some { s with pc:=l }
  | jzero l,s => some { s with pc:=if s.acc=0 then l else s.pc + 1 }
  | jgtz l,s => some { s with pc:=if 0 < s.acc then l else s.pc + 1 }
  | halt,_ => none

def step (w:ℕ) (p:Program) (s:State):Option State:=
  p[s.pc]?.bind fun i => i.effect w s

end Lax759944Proofs.Microcode

end

section

namespace Lax759944Proofs.RamToTM

open Polynomial

theorem polynomial_eval_le_coeffSum_mul (p:Polynomial ℕ) (n:ℕ):
    p.eval n≤ polyCoeffSum p * (n + 1) ^ p.natDegree:=by
  rw [Polynomial.eval_eq_sum]
  calc
    p.sum (fun i a => a * n ^ i)≤
        p.support.sum (fun i => p.coeff i * (n + 1) ^ p.natDegree):=by
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_left (by omega) i).trans
        (Nat.pow_le_pow_right (by omega) (Polynomial.le_natDegree_of_mem_supp i hi))
    _=polyCoeffSum p * (n + 1) ^ p.natDegree:=by
      rw [polyCoeffSum,Finset.sum_mul]

@[simp] theorem polynomialSimpleMajorant_eval (p:Polynomial ℕ) (n:ℕ):
    (polynomialSimpleMajorant p).eval n =
      polyCoeffSum p * (n + 1) ^ p.natDegree:=by
  simp [polynomialSimpleMajorant]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive MoveStack | source | target
  deriving DecidableEq,Fintype,Inhabited

inductive MoveLabel | loop | done
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive CompareStack | left | right | leftBackup | rightBackup
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive LookupCellStack
  | source | address | value | cellBackup | query | addressBackup | queryBackup
  deriving DecidableEq,Fintype,Inhabited

inductive LookupCellLabel | address | value | cellEnd | compare | done
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem sparseBitDecode_encode (b:Bool):
    sparseBitDecode (sparseBitEncode b)=b:=rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def divStacks (dividend divisor remainder quotient divisorBackup remainderBackup
    differenceReverse shiftTemp:List Bool):DivStack→ List Bool
  | .dividend => dividend
  | .divisor => divisor
  | .remainder => remainder
  | .quotient => quotient
  | .divisorBackup => divisorBackup
  | .remainderBackup => remainderBackup
  | .differenceReverse => differenceReverse
  | .shiftTemp => shiftTemp

def divCfg (label:DivLabel) (state:DivControl)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):divMachine.Cfg where
  l:=some label
  var:=state
  stk:=divStacks dividend divisor remainder quotient divisorBackup remainderBackup
    differenceReverse shiftTemp

def divCleanCfg (label:DivLabel) (divisorNonzero:Bool)
    (dividend divisor remainder quotient divisorBackup:List Bool):
    divMachine.Cfg:=
  divCfg label { (default:DivControl) with divisorNonzero:=divisorNonzero }
    dividend divisor remainder quotient divisorBackup [] [] []

def divPhaseCfg (label:DivLabel) (selected borrow:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):divMachine.Cfg:=
  divCfg label
    { (default:DivControl) with
      selected:=selected,borrow:=borrow,
      divisorNonzero:=true }
    dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp

@[simp] theorem div_step_dispatch_false
    (dividend divisor remainder quotient:List Bool):
    divMachine.step (divCleanCfg .dispatch false dividend divisor remainder quotient []) =
      some (divCleanCfg .zeroLoop false dividend divisor remainder quotient []):=by
  rfl

@[simp] theorem div_step_dispatch_true
    (dividend divisor remainder quotient:List Bool):
    divMachine.step (divCleanCfg .dispatch true dividend divisor remainder quotient []) =
      some (divCleanCfg .outer true dividend divisor remainder quotient []):=by
  rfl

@[simp] theorem div_step_choose_true (selected:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
  rfl

@[simp] theorem div_step_choose_false (selected:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
  rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

inductive DispatchLabel (p:Program)
  | fetch (pc:BoundedPC p)
  | stopped
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def controlDispatchCfg (p:Program) (label:ControlDispatchLabel p)
    (state:DispatchControl) (tapes:CoreStack→ List SparseSymbol):
    (controlDispatchMachine p).Cfg where
  l:=some label
  var:=state
  stk:=tapes

@[simp] theorem control_step_stopped (p:Program) (state:DispatchControl)
    (tapes:CoreStack→ List SparseSymbol):
    (controlDispatchMachine p).step
      (controlDispatchCfg p .stopped state tapes) =
      some { l:=none,var:=state,stk:=tapes }:=by
  rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def renamedStacks {α K K':Type} (e:StackRenaming K K')
    (inner:K→ List α) (ambient:K'→ List α):K'→ List α:=
  fun k' => match e.decode k' with
    | some k => inner k
    | none => ambient k'

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem renamedStacks_literal_accumulator
    (inner:LiteralWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks literalWordCoreRenaming inner ambient .accumulator =
      inner .query:=by rfl

@[simp] theorem renamedStacks_literal_result
    (inner:LiteralWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks literalWordCoreRenaming inner ambient .work0 =
      inner .result:=by rfl

@[simp] theorem renamedStacks_literalQuery_result
    (inner:LiteralWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks literalQueryCoreRenaming inner ambient .work1 =
      inner .result:=by rfl

@[simp] theorem renamedStacks_zero_query
    (inner:ZeroWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks zeroWordCoreRenaming inner ambient .accumulator =
      inner .query:=by rfl

@[simp] theorem renamedStacks_zero_result
    (inner:ZeroWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks zeroWordCoreRenaming inner ambient .work0 =
      inner .result:=by rfl

@[simp] theorem renamedStacks_lookup_memory
    (inner:LookupScanStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks lookupCoreRenaming inner ambient .memory=inner .source:=by rfl

@[simp] theorem renamedStacks_lookup_value
    (inner:LookupScanStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks lookupCoreRenaming inner ambient .work0=inner .value:=by rfl

@[simp] theorem renamedStacks_lookup_query
    (inner:LookupScanStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks lookupCoreRenaming inner ambient .work1=inner .query:=by rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

def divCoreEncode:DivStack→ CoreStack
  | .dividend => .accumulator
  | .divisor => .work1
  | .remainder => .work2
  | .quotient => .work0
  | .divisorBackup => .work3
  | .remainderBackup => .work4
  | .differenceReverse => .work5
  | .shiftTemp => .work6

def divCoreDecode:CoreStack→ Option DivStack
  | .accumulator => some .dividend
  | .work1 => some .divisor
  | .work2 => some .remainder
  | .work0 => some .quotient
  | .work3 => some .divisorBackup
  | .work4 => some .remainderBackup
  | .work5 => some .differenceReverse
  | .work6 => some .shiftTemp
  | _ => none

def divCoreRenaming:StackRenaming DivStack CoreStack where
  encode:=divCoreEncode
  decode:=divCoreDecode
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k' <;> cases k <;> simp [divCoreDecode,divCoreEncode] at h ⊢

@[simp] theorem renamedStacks_binary_left
    (inner:AddStack→ List SparseSymbol) (ambient:CoreStack→ List SparseSymbol):
    renamedStacks binaryCoreRenaming inner ambient .accumulator=inner .left:=by rfl

@[simp] theorem renamedStacks_binary_result
    (inner:AddStack→ List SparseSymbol) (ambient:CoreStack→ List SparseSymbol):
    renamedStacks binaryCoreRenaming inner ambient .work0=inner .result:=by rfl

@[simp] theorem renamedStacks_mul_result
    (inner:MulStack→ List SparseSymbol) (ambient:CoreStack→ List SparseSymbol):
    renamedStacks mulCoreRenaming inner ambient .work0=inner .accumulator:=by rfl

@[simp] theorem renamedStacks_div_quotient
    (inner:DivStack→ List SparseSymbol) (ambient:CoreStack→ List SparseSymbol):
    renamedStacks divCoreRenaming inner ambient .work0=inner .quotient:=by rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def StateLens.first (σ τ:Type):StateLens σ (σ × τ) where
  get:=Prod.fst
  put:=fun outer inner => (inner,outer.2)
  get_put:=by intros; rfl
  put_get:=by intro outer; cases outer; rfl
  put_put:=by intros; rfl

def StateLens.second (σ τ:Type):StateLens τ (σ × τ) where
  get:=Prod.snd
  put:=fun outer inner => (outer.1,inner)
  get_put:=by intros; rfl
  put_get:=by intro outer; cases outer; rfl
  put_put:=by intros; rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def mapLabelCfg {K Λ Λ' σ:Type} {α:K→ Type} (encode:Λ→ Λ')
    (c:TM2.Cfg α Λ σ):TM2.Cfg α Λ' σ where
  l:=c.l.map encode
  var:=c.var
  stk:=c.stk

@[simp] theorem mapLabelCfg_var {K Λ Λ' σ:Type} {α:K→ Type}
    (encode:Λ→ Λ') (c:TM2.Cfg α Λ σ):
    (mapLabelCfg encode c).var=c.var:=rfl

@[simp] theorem mapLabelCfg_stk {K Λ Λ' σ:Type} {α:K→ Type}
    (encode:Λ→ Λ') (c:TM2.Cfg α Λ σ):
    (mapLabelCfg encode c).stk=c.stk:=rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedAddPipelineProgram_done:
    closedAddPipelineProgram closedAddDone=.halt:=rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedAccInstallProgram_done:
    closedAccInstallProgram closedAccInstallDone=.halt:=rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedZipProgram_done (f:Bool -> Bool -> Bool):
    closedZipProgram f closedZipDone=.halt:=rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

attribute [local instance] Lax759944Proofs.RamToTM.instDecidableEqClosedMulLabel

@[simp] theorem closedMulProgram_done:
    closedMulProgram closedMulDone=.halt:=rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem subLens_get_moveLens_put {N:Nat}
    (state:FullInterpreterState N) (move:SymbolMoveControl):
    FullInterpreterState.subLens.get
      (FullInterpreterState.moveLens.put state move) =
    FullInterpreterState.subLens.get state:=by
  rfl

@[simp] theorem subtractInstallZero_moveLens_put {N:Nat}
    (state:FullInterpreterState N) (move:SymbolMoveControl):
    subtractInstallZero (FullInterpreterState.moveLens.put state move) =
      subtractInstallZero state:=by
  rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

noncomputable section

def instructionLabelType (p:Program) (pc:BoundedPC p):Type:=
  match pc.fetch with
  | some (.read a) => ReadInstructionLabel a (BoundedPC p)
  | some (.write o) => WriteInstructionLabel o (BoundedPC p)
  | some (.load o) => LoadInstructionLabel o (BoundedPC p)
  | some (.store a) => StoreInstructionLabel a (BoundedPC p)
  | some (.storeInd a) => StoreIndInstructionLabel a (BoundedPC p)
  | some (.add o) => AddInstructionLabel o (BoundedPC p)
  | some (.sub o) => SubtractInstructionLabel o (BoundedPC p)
  | some (.mul o) => MulInstructionLabel o (BoundedPC p)
  | some (.div o) => DivideInstructionTotalLabel o (BoundedPC p)
  | some (.and o) | some (.or o) | some (.xor o) | some (.compl o) =>
      ZipInstructionLabel o (BoundedPC p)
  | some (.shiftl o) | some (.shiftr o) =>
      ShiftInstructionLabel o (BoundedPC p)
  | _ => PUnit

noncomputable instance instructionLabelTypeFintype (p:Program)
    (pc:BoundedPC p):Fintype (instructionLabelType p pc):=by
  unfold instructionLabelType
  split <;> infer_instance

inductive InterpreterLabel (p:Program) (N:Nat)
  | fetch (pc:BoundedPC p)
  | data (pc:BoundedPC p)
      (code:Fin (Fintype.card (instructionLabelType p pc)))
  | control (label:ControlDispatchLabel p)
  deriving Fintype,Inhabited

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

noncomputable section

@[simp] theorem coreSimulationPolynomial_eval
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (coreSimulationPolynomial wordBound timeBound).eval n =
      1000 * timeBound.eval n * (timeBound.eval n + 1) *
        (wordBound.eval n + 2) ^ 2:=by
  simp [coreSimulationPolynomial]

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Lax759944.BinaryWordEncoding

noncomputable section

def scanOutputBits:Bool -> List Bool -> List Symbol -> Bool × List Symbol
  | seen, [],output => (seen,output)
  | seen,bit::bits,output =>
      if bit then scanOutputBits true bits (.one::output)
      else if seen then scanOutputBits true bits (.zero::output)
      else scanOutputBits false bits output

@[simp] theorem scanOutputBits_nil (seen:Bool) (output:List Symbol):
    scanOutputBits seen [] output=(seen,output):=rfl

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive UnaryMulLabel | outer | copy | restore | done
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive UnaryPowerLabel:Nat→ Type
  | done:UnaryPowerLabel 0
  | mul {d:Nat} (label:UnaryMulLabel):UnaryPowerLabel (d + 1)
  | move {d:Nat}:UnaryPowerLabel (d + 1)
  | next {d:Nat} (label:UnaryPowerLabel d):UnaryPowerLabel (d + 1)

def unaryPowerCost (a b:Nat):Nat→ Nat
  | 0 => 0
  | d + 1 =>
      a * (2 * b + 3) + 2 + a * b + 1 + unaryPowerCost (a * b) b d

@[simp] theorem unaryPowerCostPolynomial_eval
    (accumulator multiplier:Polynomial Nat) (d n:Nat):
    (unaryPowerCostPolynomial accumulator multiplier d).eval n =
      unaryPowerCost (accumulator.eval n) (multiplier.eval n) d:=by
  induction d generalizing accumulator with
  | zero => simp [unaryPowerCostPolynomial,unaryPowerCost]
  | succ d ih =>
      simp [unaryPowerCostPolynomial,unaryPowerCost,ih]

@[simp] theorem simpleMajorantEvalCostPolynomial_eval
    (p:Polynomial Nat) (n:Nat):
    (simpleMajorantEvalCostPolynomial p).eval n =
      unaryPowerCost (polyCoeffSum p) (n + 1) p.natDegree:=by
  simp [simpleMajorantEvalCostPolynomial]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Polynomial
open Lax759944.BinaryWordEncoding

noncomputable section

@[simp] theorem fullInputCostPolynomial_eval (p:Polynomial Nat) (n:Nat):
    (fullInputCostPolynomial p).eval n =
      let w:=(polynomialSimpleMajorant p).eval n + 1
      (4 * n + (simpleMajorantEvalCostPolynomial p).eval n + 5) + 1 +
      (2 * w + 3 + (n * (2 * w + 4) + 2)) + 1 +
      (n + 2 * w + 5) +
      (1 + (n + 1) * (3 * w + 5) + 1) +
      ((n + 1) * (w + 1) + 4) +
      (3 * w + (n + 1) + 5):=by
  simp [fullInputCostPolynomial,simulationWidthPolynomial]

end

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.CellToMicrocode

@[simp] theorem block_length (i:Lax759944Proofs.Legacy.Ram.Instr):(block i).length=3:=rfl

end Lax759944Proofs.CellToMicrocode

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Polynomial Lax759944Proofs.Microcode
open Lax759944.BinaryWordEncoding

noncomputable section

@[simp] theorem terminalCostPolynomial_eval
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (terminalCostPolynomial wordBound timeBound).eval n =
      2 * timeBound.eval n *
          (12 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 22) +
        28 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 65:=by
  simp [terminalCostPolynomial]

@[simp] theorem middleCostPolynomial_eval
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (middleCostPolynomial wordBound timeBound).eval n =
      (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) timeBound).eval n +
        (terminalCostPolynomial wordBound timeBound).eval n + 1:=by
  simp [middleCostPolynomial]

@[simp] theorem initialCoreSizePolynomial_eval
    (wordBound:Polynomial Nat) (n:Nat):
    (initialCoreSizePolynomial wordBound).eval n =
      ((polynomialSimpleMajorant wordBound).eval n + 1) +
        (n + 1) * ((polynomialSimpleMajorant wordBound).eval n + 2) + 3:=by
  simp [initialCoreSizePolynomial]

@[simp] theorem cleanupCostPolynomial_eval (p:Program)
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (cleanupCostPolynomial p wordBound timeBound).eval n =
      let pushes:=programPushBound
        (middleProgram p (programArgumentBound p) le_rfl)
      2 * (13 * ((initialCoreSizePolynomial wordBound).eval n +
        pushes * (middleCostPolynomial wordBound timeBound).eval n)) + 13:=by
  simp [cleanupCostPolynomial]

@[simp] theorem outputCostPolynomial_eval
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (outputCostPolynomial wordBound timeBound).eval n =
      4 + timeBound.eval n *
        (3 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 3):=by
  simp [outputCostPolynomial]

@[simp] theorem ramToTMTimePolynomial_eval (p:Program)
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (ramToTMTimePolynomial p wordBound timeBound).eval n =
      (fullInputCostPolynomial wordBound).eval n + 2 +
      (middleCostPolynomial wordBound timeBound).eval n +
      (outputCostPolynomial wordBound timeBound).eval n +
      (cleanupCostPolynomial p wordBound timeBound).eval n + 1:=by
  simp [ramToTMTimePolynomial]

end

end Lax759944Proofs.RamToTM

end

section

noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open Polynomial Lax759944Proofs.RamToTM Lax759944Proofs.Microcode

def interpreterEnvelope (W:Polynomial ℕ):Polynomial ℕ:=
  fullInputCostPolynomial W+2+middleCostPolynomial W X+outputCostPolynomial W X+
    26*initialCoreSizePolynomial W+14+26*middleCostPolynomial W X

 theorem interpreter_bound (p:Lax759944Proofs.Microcode.Program) (W:Polynomial ℕ) (n:ℕ):
    (ramToTMTimePolynomial p W X).eval n≤
      (programPushBound (middleProgram p (programArgumentBound p) le_rfl)+1)*
        (interpreterEnvelope W).eval n:=by
  simp only [ramToTMTimePolynomial_eval,cleanupCostPolynomial_eval]
  simp only [interpreterEnvelope,eval_add,eval_mul,eval_ofNat]
  nlinarith only [Nat.zero_le ((fullInputCostPolynomial W).eval n),
    Nat.zero_le ((middleCostPolynomial W X).eval n),
    Nat.zero_le ((outputCostPolynomial W X).eval n),
    Nat.zero_le ((initialCoreSizePolynomial W).eval n),
    Nat.zero_le (programPushBound (middleProgram p (programArgumentBound p) le_rfl))]

 theorem fixed_width_universal_exponent:∃ q:ℕ,0<q∧ ∀ p:Lax759944Proofs.Microcode.Program,∃ K:ℕ,0<K∧ ∀ n,
    ((ramToTMTimePolynomial p ((2*X+1)+X+C 7) X).comp (C 100*(X+1))).eval n≤ K*(n+1)^q:=by
  let U:=(interpreterEnvelope ((2*X+1)+X+C 7)).comp (C 100*(X+1))
  refine ⟨max 1 U.natDegree,by omega,?_⟩
  intro p
  let a:=programPushBound (middleProgram p (programArgumentBound p) le_rfl)+1
  refine ⟨a*(polyCoeffSum U+1),by positivity,?_⟩
  intro n
  have h:=interpreter_bound p ((2*X+1)+X+C 7) ((C 100*(X+1)).eval n)
  have hU:=polynomial_eval_le_coeffSum_mul U n
  have hp:(n+1)^U.natDegree≤ (n+1)^(max 1 U.natDegree):=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  simp only [eval_comp]
  change _≤ a*(polyCoeffSum U+1)*(n+1)^max 1 U.natDegree
  calc
    _≤ a*U.eval n:=by simpa only [U,eval_comp] using h
    _≤ a*(polyCoeffSum U*(n+1)^U.natDegree):=Nat.mul_le_mul_left a hU
    _≤ a*((polyCoeffSum U+1)*(n+1)^max 1 U.natDegree):=
      Nat.mul_le_mul_left a (Nat.mul_le_mul (by omega) hp)
    _=_:=by ring

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

namespace Lax759944Proofs.TapeRamVirtualMemory

open Lax808846.Ram

def merge (memory scratch:Nat→ Nat) (address:Nat):Nat:=
  if address % 2=0 then memory (address / 2) else scratch (address / 2)

theorem merge_even (memory scratch:Nat→ Nat) (a:Nat):
    merge memory scratch (2 * a)=memory a:=by
  simp [merge,Nat.mul_div_right]

theorem merge_odd (memory scratch:Nat→ Nat) (a:Nat):
    merge memory scratch (2 * a + 1)=scratch a:=by
  simp [merge,Nat.add_div,Nat.mul_div_right]

theorem even_address_lt (v a:Nat):2 * (a % 2 ^ v) < 2 ^ (v + 1):=by
  have:=Nat.mod_lt a (Nat.two_pow_pos v)
  rw [Nat.pow_succ]
  omega

theorem odd_address_lt (v a:Nat):2 * (a % 2 ^ v) + 1 < 2 ^ (v + 1):=by
  have:=Nat.mod_lt a (Nat.two_pow_pos v)
  rw [Nat.pow_succ]
  omega

theorem mod_physical_virtual (v value:Nat):
    value % 2 ^ (v + 1) % 2 ^ v=value % 2 ^ v:=by
  apply Nat.mod_mod_of_dvd
  exact ⟨2,Nat.pow_succ 2 v⟩

theorem set_virtual (v:Nat) (memory scratch:Nat→ Nat) (a value:Nat):
    setCell (v + 1) (merge memory scratch) (2 * (a % 2 ^ v)) (value % 2 ^ v) =
      merge (setCell v memory a value) scratch:=by
  funext address
  have hvalue:value % 2 ^ v < 2 ^ (v + 1):=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos v))
      (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [setCell,Nat.mod_eq_of_lt (even_address_lt v a),
    Nat.mod_eq_of_lt hvalue,merge]
  by_cases heven:address % 2=0
  · simp only [heven, ↓reduceIte]
    have heq:address=2 * (a % 2 ^ v)↔ address / 2=a % 2 ^ v:=by omega
    simp only [heq]
  · have hne:address ≠ 2 * (a % 2 ^ v):=by omega
    simp [heven,hne]

theorem set_scratch (v:Nat) (memory scratch:Nat→ Nat) (a value:Nat):
    setCell (v + 1) (merge memory scratch) (2 * (a % 2 ^ v) + 1) value =
      merge memory
        (fun b => if b=a % 2 ^ v then value % 2 ^ (v + 1) else scratch b):=by
  funext address
  simp only [setCell,Nat.mod_eq_of_lt (odd_address_lt v a),merge]
  by_cases heven:address % 2=0
  · have hne:address ≠ 2 * (a % 2 ^ v) + 1:=by omega
    simp [heven,hne]
  · simp only [heven, ↓reduceIte]
    have heq:address=2 * (a % 2 ^ v) + 1↔ address / 2=a % 2 ^ v:=by omega
    simp only [heq]

end Lax759944Proofs.TapeRamVirtualMemory

end

section

namespace Lax759944Proofs.TapeRamVirtualCompiler

open Lax808846.Ram TapeRamVirtualMemory

def twoRegister:Nat:=3
def addressRegister:Nat:=5

def resultRegister:Nat:=11

def initialCost:Program:= [.set 1 0, .not 1 1, .set 3 2, .div 1 1 3]

def readCell (target address:Nat):Program:=
  [.set 5 address, .and 5 5 1, .mul 5 5 3, .load target 5]

def writeCell (address:Nat):Program:=
  [.set 5 address, .and 5 5 1, .mul 5 5 3, .and 11 11 1, .store 5 11]

def body:Instr→ Program
  | .set a value => [.set 11 value] ++ writeCell a
  | .load a b => readCell 7 b ++ [.mul 5 7 3, .load 11 5] ++ writeCell a
  | .store a b => readCell 7 a ++ readCell 11 b ++
      [.mul 5 7 3, .and 11 11 1, .store 5 11]
  | .add a b c => readCell 7 b ++ readCell 9 c ++ [.add 11 7 9] ++ writeCell a
  | .sub a b c => readCell 7 b ++ readCell 9 c ++ [.sub 11 7 9] ++ writeCell a
  | .mul a b c => readCell 7 b ++ readCell 9 c ++ [.mul 11 7 9] ++ writeCell a
  | .div a b c => readCell 7 b ++ readCell 9 c ++ [.div 11 7 9] ++ writeCell a
  | .and a b c => readCell 7 b ++ readCell 9 c ++ [.and 11 7 9] ++ writeCell a
  | .shiftl a b c => readCell 7 b ++ readCell 9 c ++ [.shiftl 11 7 9] ++ writeCell a
  | .not a b => readCell 7 b ++ [.sub 11 1 7] ++ writeCell a
  | .inputLength a => [.inputLength 11] ++ writeCell a
  | .inputLoad a b => readCell 7 b ++ [.inputLoad 11 7] ++ writeCell a
  | .read a => [.read 11] ++ writeCell a
  | .write a => readCell 11 a ++ [.write 11]
  | .jzero a _ => readCell 11 a
  | .jump _ | .jeof _ | .halt => []

theorem body_length_le (i:Instr):(body i).length≤ 16:=by
  cases i <;> simp [body,readCell,writeCell]

def paddedBody (i:Instr):Program:=
  body i ++ List.replicate (16 - (body i).length) (.set 5 0)

@[simp] theorem paddedBody_length (i:Instr):(paddedBody i).length=16:=by
  simp only [paddedBody,List.length_append,List.length_replicate]
  have:=body_length_le i
  omega

def location (pc:Nat):Nat:=4 + 18 * pc

def branch (pc:Nat):Instr→ Program
  | .halt => [.halt, .halt]
  | .jump target => [.jump (location target), .halt]
  | .jzero _ target => [.jzero 11 (location target), .jump (location (pc + 1))]
  | .jeof target => [.jeof (location target), .jump (location (pc + 1))]
  | _ => [.jump (location (pc + 1)), .halt]

def block (pc:Nat) (i:Instr):Program:=
  paddedBody i ++ branch pc i

def blocks (pc:Nat):Program→ Program
  | [] => []
  | i::rest => block pc i ++ blocks (pc + 1) rest

def compile (p:Program):Program:=initialCost ++ blocks 0 p

@[simp] theorem branch_length (pc:Nat) (i:Instr):(branch pc i).length=2:=by
  cases i <;> rfl

@[simp] theorem block_length (pc:Nat) (i:Instr):(block pc i).length=18:=by
  simp [block]

@[simp] theorem blocks_length (pc:Nat) (p:Program):
    (blocks pc p).length=18 * p.length:=by
  induction p generalizing pc with
  | nil => rfl
  | cons i rest ih => simp only [blocks,List.length_append,block_length,ih,
      List.length_cons]; omega

@[simp] theorem compile_length (p:Program):(compile p).length=location p.length:=by
  simp [compile,initialCost,location]
  omega

theorem blocks_get (p:Program) (base pc offset:Nat) (hoff:offset < 18):
    (blocks base p)[18 * pc + offset]? =
      p[pc]?.bind (fun i => (block (base + pc) i)[offset]?):=by
  induction p generalizing base pc with
  | nil => simp [blocks]
  | cons i rest ih =>
    cases pc with
    | zero => simp [blocks,List.getElem?_append,hoff]
    | succ pc =>
      have hlarge:¬18 * (pc + 1) + offset < 18:=by omega
      simp only [blocks,List.getElem?_append,block_length,hlarge, ↓reduceIte,
        List.getElem?_cons_succ]
      rw [show 18 * (pc + 1) + offset - 18=18 * pc + offset by omega,ih]
      simp [Nat.add_comm,Nat.add_left_comm]

theorem compile_get (p:Program) (pc offset:Nat) (hoff:offset < 18):
    (compile p)[location pc + offset]? =
      p[pc]?.bind (fun i => (block pc i)[offset]?):=by
  have hlarge:¬location pc + offset < initialCost.length:=by simp [location,initialCost]; omega
  simp only [compile,List.getElem?_append,hlarge, ↓reduceIte]
  have hsub:location pc + offset - initialCost.length=18 * pc + offset:=by
    simp [location,initialCost]; omega
  rw [hsub,blocks_get p 0 pc offset hoff,Nat.zero_add]

theorem compile_get_paddedBody (p:Program) (pc:Nat) (i:Instr)
    (hfetch:p[pc]?=some i) (offset:Nat) (hoff:offset < 16):
    (compile p)[location pc + offset]?=(paddedBody i)[offset]?:=by
  rw [compile_get p pc offset (by omega),hfetch]
  simp [block,List.getElem?_append,hoff]

theorem compile_get_branch (p:Program) (pc:Nat) (i:Instr)
    (hfetch:p[pc]?=some i) (offset:Nat) (hoff:offset < 2):
    (compile p)[location pc + 16 + offset]?=(branch pc i)[offset]?:=by
  rw [show location pc + 16 + offset=location pc + (16 + offset) by omega,
    compile_get p pc (16 + offset) (by omega),hfetch]
  simp [block,List.getElem?_append,hoff]

theorem half_all_ones (v:Nat):(2 ^ (v + 1) - 1) / 2=2 ^ v - 1:=by
  have:=Nat.two_pow_pos v
  rw [Nat.pow_succ]
  omega

end Lax759944Proofs.TapeRamVirtualCompiler

end

section

namespace Lax759944Proofs.TapeRamVirtualMacros

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualCompiler

def execute (w:Nat):Program→ State→ Option State
  | [],s => some s
  | i::rest,s => (i.effect w s).bind (execute w rest)

theorem execute_append (w:Nat) (first second:Program) (s:State):
    execute w (first ++ second) s =
      (execute w first s).bind (execute w second):=by
  induction first generalizing s with
  | nil => rfl
  | cons i first ih => simp [execute,ih,Option.bind_assoc]

def StraightLine:Instr→ Prop
  | .jump _ | .jzero _ _ | .jeof _ => False
  | _ => True

theorem straightLine_effect_pc (i:Instr) (hlinear:StraightLine i)
    (w:Nat) (s next:State) (heffect:i.effect w s=some next):
    next.pc=s.pc + 1:=by
  cases i <;> simp only [StraightLine] at hlinear
  all_goals try contradiction
  all_goals simp only [Instr.effect] at heffect
  all_goals try { cases heffect; rfl }
  case read a =>
    cases hi:s.inp.head? with
    | none => rw [hi] at heffect; cases heffect
    | some value => rw [hi] at heffect; cases heffect; rfl

theorem run_eq_execute (w:Nat) (p code:Program) (s:State)
    (hlinear:∀ i∈ code,StraightLine i)
    (hfetch:∀ k,k < code.length→ p[s.pc + k]?=code[k]?):
    run w p code.length s=execute w code s:=by
  induction code generalizing s with
  | nil => rfl
  | cons i code ih =>
    have hfirst:p[s.pc]?=some i:=by simpa using hfetch 0 (by simp)
    simp only [List.length_cons,run,step,hfirst,Option.bind_some,execute]
    cases heffect:i.effect w s with
    | none => rfl
    | some next =>
      simp only [Option.bind_some]
      have hpc:=straightLine_effect_pc i (hlinear i (by simp)) w s next heffect
      apply ih next
      · intro j hj
        exact hlinear j (by simp [hj])
      · intro k hk
        have:=hfetch (k + 1) (by simp; omega)
        simpa [hpc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using this

theorem run_add (w:Nat) (p:Program) (first second:Nat) (s:State):
    run w p (first + second) s=(run w p first s).bind (run w p second):=by
  induction first generalizing s with
  | zero => simp [run]
  | succ first ih =>
      simp only [Nat.succ_add,run]
      cases hstep:step w p s with
      | none => rfl
      | some next =>
          simp only [Option.bind_some]
          exact ih next

def put (scratch:Nat→ Nat) (index value:Nat):Nat→ Nat:=
  fun a => if a=index then value else scratch a

@[simp] theorem put_same (scratch:Nat→ Nat) (index value:Nat):
    put scratch index value index=value:=by simp [put]

@[simp] theorem put_other (scratch:Nat→ Nat) (index value a:Nat) (h:a ≠ index):
    put scratch index value a=scratch a:=by simp [put,h]

@[simp] theorem put_overwrite (scratch:Nat→ Nat) (index first second:Nat):
    put (put scratch index first) index second=put scratch index second:=by
  funext a
  by_cases ha:a=index <;> simp [put,ha]

def state (original:List Nat) (pc:Nat) (memory scratch:Nat→ Nat) (input output:List Nat):State:=
  ⟨pc,merge memory scratch,original,input,output⟩

variable {original:List Nat}

def Normalized (v:Nat) (memory:Nat→ Nat):Prop:=
  ∀ address,memory address < 2 ^ v

def CompilerScratch (v:Nat) (scratch:Nat→ Nat):Prop:=
  scratch 0=2 ^ v - 1∧ scratch 1=2

def ScratchPreservedFrom (threshold:Nat) (before after:Nat→ Nat):Prop:=
  ∀ index,threshold≤ index→ after index=before index

theorem scratchPreservedFrom_refl (threshold:Nat) (scratch:Nat→ Nat):
    ScratchPreservedFrom threshold scratch scratch:=by
  intro index hindex
  rfl

theorem ScratchPreservedFrom.trans {threshold:Nat} {first second third:Nat→ Nat}
    (hfirst:ScratchPreservedFrom threshold first second)
    (hsecond:ScratchPreservedFrom threshold second third):
    ScratchPreservedFrom threshold first third:=by
  intro index hindex
  rw [hsecond index hindex,hfirst index hindex]

theorem scratchPreservedFrom_put (threshold:Nat) (scratch:Nat→ Nat)
    (index value:Nat) (hindex:index < threshold):
    ScratchPreservedFrom threshold scratch (put scratch index value):=by
  intro other hother
  simp [put]
  omega

theorem normalized_setCell (v:Nat) (memory:Nat→ Nat)
    (h:Normalized v memory) (address value:Nat):
    Normalized v (setCell v memory address value):=by
  intro a
  simp only [setCell]
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos v)
  · exact h a

theorem compilerScratch_put (v:Nat) (scratch:Nat→ Nat)
    (h:CompilerScratch v scratch) (index value:Nat) (hindex:2≤ index):
    CompilerScratch v (put scratch index value):=by
  rcases h with ⟨hmask,htwo⟩
  constructor <;> simp [put,hmask,htwo] <;> omega

theorem set_odd (v:Nat) (memory scratch:Nat→ Nat) (address value:Nat)
    (hodd:address % 2=1) (hbound:address < 2 ^ (v + 1)):
    setCell (v + 1) (merge memory scratch) address value =
      merge memory (put scratch (address / 2) (value % 2 ^ (v + 1))):=by
  have hindex:address / 2 < 2 ^ v:=by rw [Nat.pow_succ] at hbound; omega
  have heq:2 * (address / 2) + 1=address:=by omega
  simpa only [Nat.mod_eq_of_lt hindex,heq,put] using!
    set_scratch v memory scratch (address / 2) value

theorem setRegister_execute (v pc target value:Nat)
    (memory scratch:Nat→ Nat) (input output:List Nat)
    (htarget:2 * target + 1 < 2 ^ (v + 1)):
    execute (v + 1) [.set (2 * target + 1) value]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target (value % 2 ^ (v + 1))) input output):=by
  have hmod:=Nat.mod_eq_of_lt htarget
  have hset:=set_odd v memory scratch (2 * target + 1) value (by omega) htarget
  simp only [execute,state,Instr.effect,hmod,hset,Option.bind_some]
  simpa [Nat.add_div,Nat.mul_div_right]

theorem readRegister_execute (v pc target value:Nat) (rest:List Nat)
    (memory scratch:Nat→ Nat) (output:List Nat)
    (htarget:2 * target + 1 < 2 ^ (v + 1)):
    execute (v + 1) [.read (2 * target + 1)]
      (state original pc memory scratch (value::rest) output) =
      some (state original (pc + 1) memory
        (put scratch target (value % 2 ^ (v + 1))) rest output):=by
  have hmod:=Nat.mod_eq_of_lt htarget
  have hset:=set_odd v memory scratch (2 * target + 1) value (by omega) htarget
  simp only [execute,state,Instr.effect,List.head?_cons,Option.map_some,
    List.tail_cons,hmod,hset,Option.bind_some]
  simpa [Nat.add_div,Nat.mul_div_right]

inductive BinaryKind
  | add | sub | mul | div | and | shiftl

def BinaryKind.instruction (kind:BinaryKind) (target left right:Nat):Instr:=
  match kind with
  | .add => .add target left right
  | .sub => .sub target left right
  | .mul => .mul target left right
  | .div => .div target left right
  | .and => .and target left right
  | .shiftl => .shiftl target left right

def BinaryKind.value (kind:BinaryKind) (left right:Nat):Nat:=
  match kind with
  | .add => left + right
  | .sub => left - right
  | .mul => left * right
  | .div => left / right
  | .and => Nat.land left right
  | .shiftl => left * 2 ^ right

theorem binaryRegister_execute (kind:BinaryKind) (v pc target left right:Nat)
    (memory scratch:Nat→ Nat) (input output:List Nat)
    (htarget:2 * target + 1 < 2 ^ (v + 1))
    (hleft:2 * left + 1 < 2 ^ (v + 1))
    (hright:2 * right + 1 < 2 ^ (v + 1)):
    execute (v + 1) [kind.instruction (2 * target + 1) (2 * left + 1) (2 * right + 1)]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target (kind.value (scratch left) (scratch right) % 2 ^ (v + 1)))
        input output):=by
  have ht:=Nat.mod_eq_of_lt htarget
  have hl:=Nat.mod_eq_of_lt hleft
  have hr:=Nat.mod_eq_of_lt hright
  have hset:=set_odd v memory scratch (2 * target + 1)
    (kind.value (scratch left) (scratch right)) (by omega) htarget
  cases kind <;> simp only [execute,BinaryKind.instruction,BinaryKind.value,
    state,Instr.effect,ht,hl,hr,merge_odd,Option.bind_some]
  all_goals simpa [BinaryKind.value,Nat.add_div,Nat.mul_div_right] using hset

theorem body_straightLine (i:Instr):∀ j∈ body i,StraightLine j:=by
  cases i <;> simp [body,readCell,writeCell,StraightLine]

theorem padding_execute (v count pc:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧ nextScratch 5=scratch 5∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (List.replicate count (.set 5 0))
        (state original pc memory scratch input output) =
        some (state original (pc + count) memory nextScratch input output):=by
  induction count generalizing pc scratch with
  | zero =>
      exact ⟨scratch,hscratch,rfl,scratchPreservedFrom_refl 6 scratch,
        by simp [execute]⟩
  | succ count ih =>
      let afterSet:=put scratch 2 0
      have hsAfter:CompilerScratch v afterSet:=
        compilerScratch_put v scratch hscratch 2 0 (by omega)
      rcases ih (pc:=pc + 1) (scratch:=afterSet) hsAfter with
        ⟨nextScratch,hsNext,hfive,hhigh,hexecute⟩
      refine ⟨nextScratch,hsNext, ?_, ?_, ?_⟩
      · rw [hfive]
        simp [afterSet]
      · exact (scratchPreservedFrom_put 6 scratch 2 0 (by omega)).trans hhigh
      · rw [List.replicate_succ]
        change execute (v + 1)
          ([Instr.set 5 0] ++ List.replicate count (Instr.set 5 0))
          (state original pc memory scratch input output)=_
        rw [execute_append,
          setRegister_execute v pc 2 0 memory scratch input output (by omega)]
        simp only [Nat.zero_mod,Option.bind_some]
        change execute (v + 1) (List.replicate count (Instr.set 5 0))
          (state original (pc + 1) memory afterSet input output)=_
        rw [hexecute]
        congr 2
        omega

theorem prelude_execute (v pc:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1)):
    execute (v + 1) initialCost (state original pc memory scratch input output) =
      some (state original (pc + 4) memory (put (put scratch 1 2) 0 (2 ^ v - 1)) input output):=by
  have h1:1 % 2 ^ (v + 1)=1:=Nat.mod_eq_of_lt (by omega)
  have h2:2 % 2 ^ (v + 1)=2:=Nat.mod_eq_of_lt (by omega)
  have h3:3 % 2 ^ (v + 1)=3:=Nat.mod_eq_of_lt (by omega)
  have hset1 (sc:Nat→ Nat) (value:Nat):
      setCell (v + 1) (merge memory sc) 1 value =
        merge memory (put sc 0 (value % 2 ^ (v + 1))):=
    set_odd v memory sc 1 value (by decide) (by omega)
  have hset3 (sc:Nat→ Nat) (value:Nat):
      setCell (v + 1) (merge memory sc) 3 value =
        merge memory (put sc 1 (value % 2 ^ (v + 1))):=
    set_odd v memory sc 3 value (by decide) (by omega)
  have hread1 (sc:Nat→ Nat):merge memory sc 1=sc 0:=by simp [merge]
  have hread3 (sc:Nat→ Nat):merge memory sc 3=sc 1:=by simp [merge]
  have hall:2 ^ (v + 1) - 1 < 2 ^ (v + 1):=by omega
  have hmask:2 ^ v - 1 < 2 ^ (v + 1):=by
    have:=Nat.two_pow_pos v
    rw [Nat.pow_succ]
    omega
  simp only [execute,initialCost,state,Instr.effect,Option.bind_some,
    h1,h2,h3,hset1,hset3,hread1,hread3,put_same,put_overwrite,
    Nat.zero_mod,Nat.sub_zero,Nat.mod_eq_of_lt hall]
  simp [put,half_all_ones,Nat.mod_eq_of_lt hmask]
  apply congrArg (merge memory)
  funext index
  by_cases hindex:index=0 <;> simp [put,hindex]

theorem compile_start (v:Nat) (p:Program) (input:List Nat)
    (hcapacity:16≤ 2 ^ (v + 1)):
    run (v + 1) (compile p) 4 (initState input) =
      some (state input 4 (fun _ => 0) (put (put (fun _ => 0) 1 2) 0 (2 ^ v - 1)) input []):=by
  have hlinear:∀ i∈ initialCost,StraightLine i:=by simp [initialCost,StraightLine]
  have hfetch:∀ k,k < initialCost.length→
      (compile p)[(initState input).pc + k]?=initialCost[k]?:=by
    intro k hk
    simp [compile,initState,List.getElem?_append,hk]
  change run (v + 1) (compile p) initialCost.length (initState input)=_
  rw [run_eq_execute _ _ _ _ hlinear hfetch]
  have hinitial:initState input=state input 0 (fun _ => 0) (fun _ => 0) input []:=by
    simp only [initState,state]
    congr 1
    funext a
    simp [merge]
  rw [hinitial]
  exact prelude_execute v 0 _ _ input [] hcapacity

theorem readCell_execute (v pc address target:Nat)
    (memory scratch:Nat→ Nat) (input output:List Nat)
    (hcapacity:16≤ 2 ^ (v + 1)) (htarget:2 * target + 1 < 2 ^ (v + 1))
    (hmask:scratch 0=2 ^ v - 1) (htwo:scratch 1=2)
    (hnormal:∀ a,memory a < 2 ^ v):
    execute (v + 1) (readCell (2 * target + 1) address)
      (state original pc memory scratch input output) =
      some (state original (pc + 4) memory
        (put (put scratch 2 (2 * (address % 2 ^ v))) target (memory (address % 2 ^ v)))
        input output):=by
  have h1:1 % 2 ^ (v + 1)=1:=Nat.mod_eq_of_lt (by omega)
  have h3:3 % 2 ^ (v + 1)=3:=Nat.mod_eq_of_lt (by omega)
  have h5:5 % 2 ^ (v + 1)=5:=Nat.mod_eq_of_lt (by omega)
  have hset5 (sc:Nat→ Nat) (value:Nat):
      setCell (v + 1) (merge memory sc) 5 value =
        merge memory (put sc 2 (value % 2 ^ (v + 1))):=
    set_odd v memory sc 5 value (by decide) (by omega)
  have hsetTarget (sc:Nat→ Nat) (value:Nat):
      setCell (v + 1) (merge memory sc) (2 * target + 1) value =
        merge memory (put sc target (value % 2 ^ (v + 1))):=by
    simpa [Nat.add_div,Nat.mul_div_right] using
      set_odd v memory sc (2 * target + 1) value (by omega) htarget
  have hread1 (sc:Nat→ Nat):merge memory sc 1=sc 0:=by simp [merge]
  have hread3 (sc:Nat→ Nat):merge memory sc 3=sc 1:=by simp [merge]
  have hread5 (sc:Nat→ Nat):merge memory sc 5=sc 2:=by simp [merge]
  have hdouble:=Nat.mod_eq_of_lt (even_address_lt v address)
  have hvalue:memory (address % 2 ^ v) < 2 ^ (v + 1):=
    Nat.lt_of_lt_of_le (hnormal _) (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [execute,readCell,state,Instr.effect,Option.bind_some,
    h1,h3,h5,hset5,hsetTarget,hread1,hread3,hread5,put_same,put_overwrite]
  congr 2
  simp [put,hmask,htwo,mod_physical_virtual,
    Nat.mul_comm (address % 2 ^ v) 2,hdouble,merge_even,Nat.mod_eq_of_lt hvalue]

theorem writeCell_execute (v pc address:Nat)
    (memory scratch:Nat→ Nat) (input output:List Nat)
    (hcapacity:16≤ 2 ^ (v + 1))
    (hmask:scratch 0=2 ^ v - 1) (htwo:scratch 1=2):
    execute (v + 1) (writeCell address) (state original pc memory scratch input output) =
      some (state original (pc + 5) (setCell v memory address (scratch 5))
        (put (put scratch 2 (2 * (address % 2 ^ v))) 5 (scratch 5 % 2 ^ v))
        input output):=by
  have h1:1 % 2 ^ (v + 1)=1:=Nat.mod_eq_of_lt (by omega)
  have h3:3 % 2 ^ (v + 1)=3:=Nat.mod_eq_of_lt (by omega)
  have h5:5 % 2 ^ (v + 1)=5:=Nat.mod_eq_of_lt (by omega)
  have h11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
  have hset5 (sc:Nat→ Nat) (value:Nat):
      setCell (v + 1) (merge memory sc) 5 value =
        merge memory (put sc 2 (value % 2 ^ (v + 1))):=
    set_odd v memory sc 5 value (by decide) (by omega)
  have hset11 (sc:Nat→ Nat) (value:Nat):
      setCell (v + 1) (merge memory sc) 11 value =
        merge memory (put sc 5 (value % 2 ^ (v + 1))):=
    set_odd v memory sc 11 value (by decide) (by omega)
  have hread1 (sc:Nat→ Nat):merge memory sc 1=sc 0:=by simp [merge]
  have hread3 (sc:Nat→ Nat):merge memory sc 3=sc 1:=by simp [merge]
  have hread5 (sc:Nat→ Nat):merge memory sc 5=sc 2:=by simp [merge]
  have hread11 (sc:Nat→ Nat):merge memory sc 11=sc 5:=by simp [merge]
  have hdouble:=Nat.mod_eq_of_lt (even_address_lt v address)
  have hsmall (value:Nat):value % 2 ^ v < 2 ^ (v + 1):=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos v))
      (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [execute,writeCell,state,Instr.effect,Option.bind_some,
    h1,h3,h5,h11,hset5,hset11,hread1,hread3,hread5,hread11,
    put_same,put_overwrite]
  simp [put,hmask,htwo,mod_physical_virtual,
    Nat.mul_comm (address % 2 ^ v) 2,hdouble,Nat.mod_eq_of_lt (hsmall _),set_virtual]

end Lax759944Proofs.TapeRamVirtualMacros

end

section

namespace Lax759944Proofs.TapeRamVirtualSimulation

open Lax808846.Ram
open TapeRamVirtualMemory TapeRamVirtualCompiler TapeRamVirtualMacros

theorem normalized_init (v:Nat) (input:List Nat):
    Normalized v (initState input).mem:=by
  intro address
  exact Nat.two_pow_pos v

theorem normalized_effect {v:Nat} {i:Instr} {source next:State}
    (hnormal:Normalized v source.mem) (heffect:i.effect v source=some next):
    Normalized v next.mem:=by
  cases i <;> simp only [Instr.effect] at heffect
  all_goals try { cases heffect; exact hnormal }
  case halt => cases heffect
  case read address =>
    cases hi:source.inp.head? with
    | none => rw [hi] at heffect; cases heffect
    | some value =>
      rw [hi] at heffect
      cases heffect
      exact normalized_setCell v source.mem hnormal address value
  all_goals
    cases heffect
    exact normalized_setCell v source.mem hnormal _ _

variable {original:List Nat}

theorem body_set (v pc address value:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.set address value))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.set address value)).length)
          (setCell v memory address value) nextScratch input output):=by
  rcases hscratch with ⟨hmask,htwo⟩
  rw [show body (.set address value)=[.set 11 value] ++ writeCell address by rfl,
    execute_append,setRegister_execute v pc 5 value memory scratch input output (by omega)]
  simp only [Option.bind_some]
  rw [writeCell_execute v (pc + 1) address memory
    (put scratch 5 (value % 2 ^ (v + 1))) input output hcapacity]
  · let nextScratch:=
      put (put (put scratch 5 (value % 2 ^ (v + 1))) 2
        (2 * (address % 2 ^ v))) 5 (value % 2 ^ v)
    refine ⟨nextScratch, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v scratch ⟨hmask,htwo⟩ 5 _ (by omega))
          2 _ (by omega)) 5 _ (by omega)
    · intro index hindex
      have h2:index ≠ 2:=by omega
      have h5:index ≠ 5:=by omega
      simp [nextScratch,put,h2,h5]
    simp only [body,List.length_append,List.length_cons,List.length_nil,
      Nat.add_zero,writeCell]
    dsimp [nextScratch]
    have hmemory:setCell v memory address (value % 2 ^ (v + 1)) =
        setCell v memory address value:=by
      funext a
      simp [setCell,TapeRamVirtualMemory.mod_physical_virtual]
    simp only [put_same]
    rw [hmemory]
    congr 2
    simp [put,TapeRamVirtualMemory.mod_physical_virtual]
  · simp [put,hmask]
  · simp [put,htwo]

def sourceInstruction (kind:BinaryKind) (target left right:Nat):Instr:=
  match kind with
  | .add => .add target left right
  | .sub => .sub target left right
  | .mul => .mul target left right
  | .div => .div target left right
  | .and => .and target left right
  | .shiftl => .shiftl target left right

theorem body_sourceInstruction (kind:BinaryKind) (target left right:Nat):
    body (sourceInstruction kind target left right) =
      readCell 7 left ++ readCell 9 right ++
        [kind.instruction 11 7 9] ++ writeCell target:=by
  cases kind <;> rfl

theorem body_binary (kind:BinaryKind) (v pc target left right:Nat)
    (memory scratch:Nat→ Nat) (input output:List Nat)
    (hcapacity:16≤ 2 ^ (v + 1)) (hscratch:CompilerScratch v scratch)
    (hnormal:Normalized v memory):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (sourceInstruction kind target left right))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (sourceInstruction kind target left right)).length)
          (setCell v memory target (kind.value (memory (left % 2 ^ v))
            (memory (right % 2 ^ v)))) nextScratch input output):=by
  rcases hscratch with ⟨hmask,htwo⟩
  let sLeft:=put (put scratch 2 (2 * (left % 2 ^ v))) 3 (memory (left % 2 ^ v))
  let sRight:=put (put sLeft 2 (2 * (right % 2 ^ v))) 4 (memory (right % 2 ^ v))
  let raw:=kind.value (memory (left % 2 ^ v)) (memory (right % 2 ^ v))
  let sResult:=put sRight 5 (raw % 2 ^ (v + 1))
  let nextScratch:=put (put sResult 2 (2 * (target % 2 ^ v))) 5 (raw % 2 ^ v)
  have hsLeft:CompilerScratch v sLeft:=
    compilerScratch_put v _ (compilerScratch_put v scratch ⟨hmask,htwo⟩ 2 _ (by omega)) 3 _ (by omega)
  have hsRight:CompilerScratch v sRight:=
    compilerScratch_put v _ (compilerScratch_put v sLeft hsLeft 2 _ (by omega)) 4 _ (by omega)
  have hsResult:CompilerScratch v sResult:=compilerScratch_put v sRight hsRight 5 _ (by omega)
  have hsNext:CompilerScratch v nextScratch:=
    compilerScratch_put v _ (compilerScratch_put v sResult hsResult 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch,hsNext, ?_, ?_⟩
  · intro index hindex
    have h2:index ≠ 2:=by omega
    have h3:index ≠ 3:=by omega
    have h4:index ≠ 4:=by omega
    have h5:index ≠ 5:=by omega
    simp [nextScratch,sResult,sRight,sLeft,put,h2,h3,h4,h5]
  rw [body_sourceInstruction,execute_append,execute_append,execute_append]
  rw [readCell_execute v pc left 3 memory scratch input output hcapacity (by omega)
    hmask htwo hnormal]
  simp only [Option.bind_some]
  rw [readCell_execute v (pc + 4) right 4 memory sLeft input output
    hcapacity (by omega) hsLeft.1 hsLeft.2 hnormal]
  simp only [Option.bind_some]
  rw [binaryRegister_execute kind v (pc + 4 + 4) 5 3 4 memory sRight
    input output (by omega) (by omega) (by omega)]
  simp only [Option.bind_some]
  have hsRightLeft:sRight 3=memory (left % 2 ^ v):=by
    simp [sRight,sLeft,put]
  have hsRightRight:sRight 4=memory (right % 2 ^ v):=by
    simp [sRight,sLeft,put]
  rw [hsRightLeft,hsRightRight]
  rw [writeCell_execute v (pc + 4 + 4 + 1) target memory sResult input output hcapacity
    hsResult.1 hsResult.2]
  have hmemory:setCell v memory target (raw % 2 ^ (v + 1)) =
      setCell v memory target raw:=by
    funext a
    simp [setCell,TapeRamVirtualMemory.mod_physical_virtual]
  simp only [sResult,put_same]
  rw [hmemory]
  dsimp [sLeft,sRight,raw,sResult,nextScratch]
  congr 2 <;> simp [put,TapeRamVirtualMemory.mod_physical_virtual,
    body_sourceInstruction,readCell,writeCell]

theorem body_read (v pc address value:Nat) (rest:List Nat)
    (memory scratch:Nat→ Nat) (output:List Nat)
    (hcapacity:16≤ 2 ^ (v + 1)) (hscratch:CompilerScratch v scratch):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.read address))
        (state original pc memory scratch (value::rest) output) =
        some (state original (pc + (body (.read address)).length)
          (setCell v memory address value) nextScratch rest output):=by
  rcases hscratch with ⟨hmask,htwo⟩
  let afterRead:=put scratch 5 (value % 2 ^ (v + 1))
  let nextScratch:=put (put afterRead 2 (2 * (address % 2 ^ v))) 5 (value % 2 ^ v)
  have hsAfter:CompilerScratch v afterRead:=
    compilerScratch_put v scratch ⟨hmask,htwo⟩ 5 _ (by omega)
  have hsNext:CompilerScratch v nextScratch:=compilerScratch_put v _
    (compilerScratch_put v afterRead hsAfter 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch,hsNext, ?_, ?_⟩
  · intro index hindex
    have h2:index ≠ 2:=by omega
    have h5:index ≠ 5:=by omega
    simp [nextScratch,afterRead,put,h2,h5]
  rw [show body (.read address)=[.read 11] ++ writeCell address by rfl,
    execute_append]
  have h11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
  have hset11:=set_odd v memory scratch 11 value (by decide) (by omega)
  simp only [execute,Instr.effect,state,List.head?_cons,List.tail_cons,
    Option.map_some,Option.bind_some,h11,hset11]
  change execute (v + 1) (writeCell address)
    (state original (pc + 1) memory afterRead rest output)=_
  rw [writeCell_execute v (pc + 1) address memory afterRead rest output hcapacity
    hsAfter.1 hsAfter.2]
  simp only [afterRead,put_same]
  have hmemory:setCell v memory address (value % 2 ^ (v + 1)) =
      setCell v memory address value:=by
    funext a
    simp [setCell,TapeRamVirtualMemory.mod_physical_virtual]
  rw [hmemory]
  dsimp [afterRead,nextScratch]
  congr 2 <;> simp [TapeRamVirtualMemory.mod_physical_virtual,writeCell]

theorem body_write (v pc address:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch) (hnormal:Normalized v memory):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.write address))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.write address)).length) memory nextScratch input
          (output ++ [memory (address % 2 ^ v)])):=by
  rcases hscratch with ⟨hmask,htwo⟩
  let nextScratch:=put (put scratch 2 (2 * (address % 2 ^ v))) 5
    (memory (address % 2 ^ v))
  have hsNext:CompilerScratch v nextScratch:=compilerScratch_put v _
    (compilerScratch_put v scratch ⟨hmask,htwo⟩ 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch,hsNext, ?_, ?_⟩
  · intro index hindex
    have h2:index ≠ 2:=by omega
    have h5:index ≠ 5:=by omega
    simp [nextScratch,put,h2,h5]
  rw [show body (.write address)=readCell 11 address ++ [.write 11] by rfl,
    execute_append,readCell_execute v pc address 5 memory scratch input output
      hcapacity (by omega) hmask htwo hnormal]
  simp only [Option.bind_some,execute,Instr.effect,state]
  have h11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
  have hvalue:memory (address % 2 ^ v) < 2 ^ (v + 1):=
    Nat.lt_of_lt_of_le (hnormal _) (Nat.pow_le_pow_right (by decide) (by omega))
  simp [h11,nextScratch,merge,put,Nat.mod_eq_of_lt hvalue,readCell]

theorem body_jzero (v pc address target:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch) (hnormal:Normalized v memory):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.jzero address target))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.jzero address target)).length) memory nextScratch
          input output)∧ nextScratch 5=memory (address % 2 ^ v):=by
  rcases hscratch with ⟨hmask,htwo⟩
  let nextScratch:=put (put scratch 2 (2 * (address % 2 ^ v))) 5
    (memory (address % 2 ^ v))
  refine ⟨nextScratch,
    compilerScratch_put v _ (compilerScratch_put v scratch ⟨hmask,htwo⟩ 2 _ (by omega))
      5 _ (by omega), ?_, ?_,by simp [nextScratch]⟩
  · intro index hindex
    have h2:index ≠ 2:=by omega
    have h5:index ≠ 5:=by omega
    simp [nextScratch,put,h2,h5]
  simpa [body,readCell] using
    readCell_execute v pc address 5 memory scratch input output hcapacity (by omega)
      hmask htwo hnormal

theorem body_not (v pc target source:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch) (hnormal:Normalized v memory):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.not target source))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.not target source)).length)
          (setCell v memory target (2 ^ v - 1 - memory (source % 2 ^ v)))
          nextScratch input output):=by
  rcases hscratch with ⟨hmask,htwo⟩
  let afterRead:=put (put scratch 2 (2 * (source % 2 ^ v))) 3
    (memory (source % 2 ^ v))
  let complement:=2 ^ v - 1 - memory (source % 2 ^ v)
  let afterSub:=put afterRead 5 complement
  let nextScratch:=put (put afterSub 2 (2 * (target % 2 ^ v))) 5 complement
  have hsRead:CompilerScratch v afterRead:=compilerScratch_put v _
    (compilerScratch_put v scratch ⟨hmask,htwo⟩ 2 _ (by omega)) 3 _ (by omega)
  have hsSub:CompilerScratch v afterSub:=compilerScratch_put v afterRead hsRead 5 _ (by omega)
  have hsNext:CompilerScratch v nextScratch:=compilerScratch_put v _
    (compilerScratch_put v afterSub hsSub 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch,hsNext, ?_, ?_⟩
  · intro index hindex
    have h2:index ≠ 2:=by omega
    have h3:index ≠ 3:=by omega
    have h5:index ≠ 5:=by omega
    simp [nextScratch,afterSub,afterRead,put,h2,h3,h5]
  rw [show body (.not target source) =
      readCell 7 source ++ [.sub 11 1 7] ++ writeCell target by rfl,
    execute_append,execute_append,
    readCell_execute v pc source 3 memory scratch input output hcapacity (by omega)
      hmask htwo hnormal]
  simp only [Option.bind_some]
  change (execute (v + 1) [.sub 11 1 7]
    (state original (pc + 4) memory afterRead input output)).bind
      (execute (v + 1) (writeCell target))=_
  have hvalue:complement < 2 ^ (v + 1):=by
    have:=Nat.two_pow_pos v
    rw [Nat.pow_succ]
    omega
  have hsubexec:execute (v + 1) [.sub 11 1 7]
      (state original (pc + 4) memory afterRead input output) =
      some (state original (pc + 4 + 1) memory
        (put afterRead 5 ((afterRead 0 - afterRead 3) % 2 ^ (v + 1))) input output):=by
    simpa [BinaryKind.instruction,BinaryKind.value] using
      binaryRegister_execute .sub v (pc + 4) 5 0 3 memory afterRead input output
        (by omega) (by omega) (by omega)
  rw [hsubexec]
  simp only [Option.bind_some]
  have hzero:afterRead 0=2 ^ v - 1:=hsRead.1
  have hthree:afterRead 3=memory (source % 2 ^ v):=by simp [afterRead]
  rw [hzero,hthree,Nat.mod_eq_of_lt hvalue]
  change execute (v + 1) (writeCell target)
    (state original (pc + 4 + 1) memory afterSub input output)=_
  rw [writeCell_execute v (pc + 4 + 1) target memory afterSub input output hcapacity
    hsSub.1 hsSub.2]
  simp only [afterSub,put_same]
  have hvirtual:complement < 2 ^ v:=by
    have:=Nat.two_pow_pos v
    omega
  dsimp [afterRead,complement,afterSub,nextScratch]
  congr 2
  rw [Nat.mod_eq_of_lt hvirtual]

theorem body_load (v pc target addressCell:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch) (hnormal:Normalized v memory):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.load target addressCell))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.load target addressCell)).length)
          (setCell v memory target (memory (memory (addressCell % 2 ^ v))))
          nextScratch input output):=by
  rcases hscratch with ⟨hmask,htwo⟩
  let pointer:=memory (addressCell % 2 ^ v)
  let afterRead:=put (put scratch 2 (2 * (addressCell % 2 ^ v))) 3 pointer
  let afterDouble:=put afterRead 2 (2 * pointer)
  let afterLoad:=put afterDouble 5 (memory pointer)
  let nextScratch:=put (put afterLoad 2 (2 * (target % 2 ^ v))) 5
    (memory pointer)
  have hpointer:pointer < 2 ^ v:=hnormal _
  have hdouble:2 * pointer < 2 ^ (v + 1):=by
    rw [Nat.pow_succ]
    omega
  have hloaded:memory pointer < 2 ^ (v + 1):=
    Nat.lt_of_lt_of_le (hnormal pointer)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hsRead:CompilerScratch v afterRead:=compilerScratch_put v _
    (compilerScratch_put v scratch ⟨hmask,htwo⟩ 2 _ (by omega)) 3 _ (by omega)
  have hsDouble:CompilerScratch v afterDouble:=
    compilerScratch_put v afterRead hsRead 2 _ (by omega)
  have hsLoad:CompilerScratch v afterLoad:=
    compilerScratch_put v afterDouble hsDouble 5 _ (by omega)
  have hsNext:CompilerScratch v nextScratch:=compilerScratch_put v _
    (compilerScratch_put v afterLoad hsLoad 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch,hsNext, ?_, ?_⟩
  · intro index hindex
    have h2:index ≠ 2:=by omega
    have h3:index ≠ 3:=by omega
    have h5:index ≠ 5:=by omega
    simp [nextScratch,afterLoad,afterDouble,afterRead,put,h2,h3,h5]
  rw [show body (.load target addressCell) =
      readCell 7 addressCell ++ [.mul 5 7 3] ++ [.load 11 5] ++
        writeCell target by rfl,
    execute_append,execute_append,execute_append,
    readCell_execute v pc addressCell 3 memory scratch input output hcapacity
      (by omega) hmask htwo hnormal]
  simp only [Option.bind_some]
  have hmul:execute (v + 1) [.mul 5 7 3]
      (state original (pc + 4) memory afterRead input output) =
      some (state original (pc + 4 + 1) memory afterDouble input output):=by
    rw [show [.mul 5 7 3] =
        [BinaryKind.instruction .mul (2 * 2 + 1) (2 * 3 + 1) (2 * 1 + 1)] by
          rfl,
      binaryRegister_execute .mul v (pc + 4) 2 3 1 memory afterRead input output
      (by omega) (by omega) (by omega)]
    change some (state original (pc + 4 + 1) memory
      (put afterRead 2 (afterRead 3 * afterRead 1 % 2 ^ (v + 1))) input output) =
      some (state original (pc + 4 + 1) memory afterDouble input output)
    have hthree:afterRead 3=pointer:=by simp [afterRead]
    rw [hthree,hsRead.2,Nat.mul_comm,Nat.mod_eq_of_lt hdouble]
  rw [hmul]
  simp only [Option.bind_some]
  have hload:execute (v + 1) [.load 11 5]
      (state original (pc + 4 + 1) memory afterDouble input output) =
      some (state original (pc + 4 + 1 + 1) memory afterLoad input output):=by
    have h5:5 % 2 ^ (v + 1)=5:=Nat.mod_eq_of_lt (by omega)
    have h11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
    have hset11:=set_odd v memory afterDouble 11 (memory pointer)
      (by decide) (by omega)
    have haddress:merge memory afterDouble 5=2 * pointer:=by
      simpa [afterDouble] using merge_odd memory afterDouble 2
    have hread:merge memory afterDouble (2 * pointer)=memory pointer:=
      merge_even memory afterDouble pointer
    have hset:setCell (v + 1) (merge memory afterDouble) 11 (memory pointer) =
        merge memory (put afterDouble 5 (memory pointer)):=by
      simpa [Nat.mod_eq_of_lt hloaded,Nat.add_div,Nat.mul_div_right] using hset11
    simp only [execute,Instr.effect,state,h5,haddress,
      Nat.mod_eq_of_lt hdouble,hread,hset,Option.bind_some]
    rfl
  rw [hload]
  simp only [Option.bind_some]
  rw [writeCell_execute v (pc + 4 + 1 + 1) target memory afterLoad input output
    hcapacity hsLoad.1 hsLoad.2]
  have hmemory:setCell v memory target (memory pointer) =
      setCell v memory target (memory (memory (addressCell % 2 ^ v))):=by
    rfl
  rw [hmemory]
  congr 2
  change put (put afterLoad 2 (2 * (target % 2 ^ v))) 5
      (afterLoad 5 % 2 ^ v)=nextScratch
  rw [show afterLoad 5=memory pointer by simp [afterLoad],
    Nat.mod_eq_of_lt (hnormal pointer)]

theorem body_store (v pc addressCell valueCell:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch) (hnormal:Normalized v memory):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.store addressCell valueCell))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.store addressCell valueCell)).length)
          (setCell v memory (memory (addressCell % 2 ^ v))
            (memory (valueCell % 2 ^ v))) nextScratch input output):=by
  rcases hscratch with ⟨hmask,htwo⟩
  let pointer:=memory (addressCell % 2 ^ v)
  let value:=memory (valueCell % 2 ^ v)
  let afterPointer:=put (put scratch 2 (2 * (addressCell % 2 ^ v))) 3 pointer
  let afterValue:=put (put afterPointer 2 (2 * (valueCell % 2 ^ v))) 5 value
  let afterDouble:=put afterValue 2 (2 * pointer)
  let nextScratch:=put afterDouble 5 value
  have hpointer:pointer < 2 ^ v:=hnormal _
  have hvalue:value < 2 ^ v:=hnormal _
  have hdouble:2 * pointer < 2 ^ (v + 1):=by
    rw [Nat.pow_succ]
    omega
  have hsPointer:CompilerScratch v afterPointer:=compilerScratch_put v _
    (compilerScratch_put v scratch ⟨hmask,htwo⟩ 2 _ (by omega)) 3 _ (by omega)
  have hsValue:CompilerScratch v afterValue:=compilerScratch_put v _
    (compilerScratch_put v afterPointer hsPointer 2 _ (by omega)) 5 _ (by omega)
  have hsDouble:CompilerScratch v afterDouble:=
    compilerScratch_put v afterValue hsValue 2 _ (by omega)
  have hsNext:CompilerScratch v nextScratch:=
    compilerScratch_put v afterDouble hsDouble 5 _ (by omega)
  refine ⟨nextScratch,hsNext, ?_, ?_⟩
  · intro index hindex
    have h2:index ≠ 2:=by omega
    have h3:index ≠ 3:=by omega
    have h5:index ≠ 5:=by omega
    simp [nextScratch,afterDouble,afterValue,afterPointer,put,h2,h3,h5]
  rw [show body (.store addressCell valueCell) =
      readCell 7 addressCell ++ readCell 11 valueCell ++ [.mul 5 7 3] ++
        [.and 11 11 1] ++ [.store 5 11] by rfl,
    execute_append,execute_append,execute_append,execute_append,
    readCell_execute v pc addressCell 3 memory scratch input output hcapacity
      (by omega) hmask htwo hnormal]
  simp only [Option.bind_some]
  rw [readCell_execute v (pc + 4) valueCell 5 memory afterPointer input output
    hcapacity (by omega) hsPointer.1 hsPointer.2 hnormal]
  simp only [Option.bind_some]
  have hmul:execute (v + 1) [.mul 5 7 3]
      (state original (pc + 4 + 4) memory afterValue input output) =
      some (state original (pc + 4 + 4 + 1) memory afterDouble input output):=by
    rw [show [.mul 5 7 3] =
        [BinaryKind.instruction .mul (2 * 2 + 1) (2 * 3 + 1) (2 * 1 + 1)] by
          rfl,
      binaryRegister_execute .mul v (pc + 4 + 4) 2 3 1 memory afterValue
        input output (by omega) (by omega) (by omega)]
    change some (state original (pc + 4 + 4 + 1) memory
      (put afterValue 2 (afterValue 3 * afterValue 1 % 2 ^ (v + 1))) input output) =
      some (state original (pc + 4 + 4 + 1) memory afterDouble input output)
    have hthree:afterValue 3=pointer:=by simp [afterValue,afterPointer]
    rw [hthree,hsValue.2,Nat.mul_comm,Nat.mod_eq_of_lt hdouble]
  rw [hmul]
  simp only [Option.bind_some]
  have hand:execute (v + 1) [.and 11 11 1]
      (state original (pc + 4 + 4 + 1) memory afterDouble input output) =
      some (state original (pc + 4 + 4 + 1 + 1) memory nextScratch input output):=by
    rw [show [.and 11 11 1] =
        [BinaryKind.instruction .and (2 * 5 + 1) (2 * 5 + 1) (2 * 0 + 1)] by
          rfl,
      binaryRegister_execute .and v (pc + 4 + 4 + 1) 5 5 0 memory afterDouble
        input output (by omega) (by omega) (by omega)]
    change some (state original (pc + 4 + 4 + 1 + 1) memory
      (put afterDouble 5 (Nat.land (afterDouble 5) (afterDouble 0) % 2 ^ (v + 1)))
        input output) =
      some (state original (pc + 4 + 4 + 1 + 1) memory nextScratch input output)
    have hfive:afterDouble 5=value:=by simp [afterDouble,afterValue]
    have hzero:afterDouble 0=2 ^ v - 1:=hsDouble.1
    have hland:Nat.land value (2 ^ v - 1)=value:=by
      change (value &&& (2 ^ v - 1))=value
      rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt hvalue]
    rw [hfive,hzero,hland,Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le hvalue (Nat.pow_le_pow_right (by decide) (by omega)))]
  rw [hand]
  simp only [Option.bind_some]
  have hstore:execute (v + 1) [.store 5 11]
      (state original (pc + 4 + 4 + 1 + 1) memory nextScratch input output) =
      some (state original (pc + 4 + 4 + 1 + 1 + 1)
        (setCell v memory pointer value) nextScratch input output):=by
    have h5:5 % 2 ^ (v + 1)=5:=Nat.mod_eq_of_lt (by omega)
    have h11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
    have haddress:merge memory nextScratch 5=2 * pointer:=by
      simpa [nextScratch,afterDouble] using merge_odd memory nextScratch 2
    have hstored:merge memory nextScratch 11=value:=by
      simpa [nextScratch] using merge_odd memory nextScratch 5
    have hset:setCell (v + 1) (merge memory nextScratch) (2 * pointer) value =
        merge (setCell v memory pointer value) nextScratch:=by
      simpa [Nat.mod_eq_of_lt hpointer,Nat.mod_eq_of_lt hvalue] using
        set_virtual v memory nextScratch pointer value
    simp only [execute,Instr.effect,state,h5,h11,haddress,hstored,hset,
      Option.bind_some]
  rw [hstore]
  congr 2

theorem body_inputLength (v pc address:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.inputLength address))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.inputLength address)).length)
          (setCell v memory address original.length) nextScratch input output):=by
  simpa only [body,List.singleton_append,List.length_cons,execute,Instr.effect,state] using
    (body_set (original:=original) v pc address original.length memory scratch
      input output hcapacity hscratch)

theorem body_inputLoad (v pc target addressCell:Nat) (memory scratch:Nat→ Nat)
    (input output:List Nat) (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch) (hnormal:Normalized v memory):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body (.inputLoad target addressCell))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.inputLoad target addressCell)).length)
          (setCell v memory target (original[memory (addressCell % 2 ^ v)]?.getD 0))
          nextScratch input output):=by
  let pointer:=memory (addressCell % 2 ^ v)
  let afterRead:=put (put scratch 2 (2 * (addressCell % 2 ^ v))) 3 pointer
  let value:=original[pointer]?.getD 0
  have hsRead:CompilerScratch v afterRead:=compilerScratch_put v _
    (compilerScratch_put v scratch hscratch 2 _ (by omega)) 3 _ (by omega)
  have hhigh:ScratchPreservedFrom 6 scratch afterRead:=by
    intro index hindex
    simp [afterRead,put,show index ≠ 2 by omega,show index ≠ 3 by omega]
  rcases body_set (original:=original) v (pc + 4) target value memory afterRead
      input output hcapacity hsRead with ⟨nextScratch,hsNext,hsHigh,hset⟩
  refine ⟨nextScratch,hsNext,hhigh.trans hsHigh, ?_⟩
  rw [show body (.inputLoad target addressCell) =
      readCell 7 addressCell ++ ([.inputLoad 11 7] ++ writeCell target) by rfl,
    execute_append,readCell_execute v pc addressCell 3 memory scratch input output
      hcapacity (by omega) hscratch.1 hscratch.2 hnormal]
  simp only [Option.bind_some]
  change execute (v + 1) ([.inputLoad 11 7] ++ writeCell target)
      (state original (pc + 4) memory afterRead input output)=_
  have h7:7 % 2 ^ (v + 1)=7:=Nat.mod_eq_of_lt (by omega)
  have hindex:pointer < 2 ^ (v + 1):=
    (hnormal _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hlookup:merge memory afterRead 7 % 2 ^ (v + 1)=pointer:=by
    rw [show merge memory afterRead 7=afterRead 3 from merge_odd memory afterRead 3,
      show afterRead 3=pointer by simp [afterRead],Nat.mod_eq_of_lt hindex]
  have htail:execute (v + 1) ([.inputLoad 11 7] ++ writeCell target)
      (state original (pc + 4) memory afterRead input output) =
      execute (v + 1) (body (.set target value))
        (state original (pc + 4) memory afterRead input output):=by
    simp only [body,List.singleton_append,execute,Instr.effect,state,h7,hlookup]
    rfl
  rw [htail,hset]
  congr 2

def BranchReady (v:Nat) (i:Instr) (source:State)
    (scratch:Nat→ Nat):Prop:=
  match i with
  | .jzero address _ => scratch 5=source.mem (address % 2 ^ v)
  | _ => True

theorem body_effect {v physicalPc:Nat} {i:Instr} {source next:State}
    {scratch:Nat→ Nat} (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch) (hnormal:Normalized v source.mem)
    (heffect:i.effect v source=some next):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧ BranchReady v i source nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (body i)
        (state source.input physicalPc source.mem scratch source.inp source.out) =
        some (state next.input (physicalPc + (body i).length) next.mem nextScratch
          next.inp next.out):=by
  cases i with
  | set address value =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_set v physicalPc address value source.mem scratch source.inp source.out
        hcapacity hscratch with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | load target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      let pointer:=source.mem (addressCell % 2 ^ v)
      have hpointer:pointer < 2 ^ v:=hnormal _
      rcases body_load v physicalPc target addressCell source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      refine ⟨nextScratch,hsNext,trivial,hhigh, ?_⟩
      simpa [pointer,Nat.mod_eq_of_lt hpointer] using hrun
  | store addressCell valueCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_store v physicalPc addressCell valueCell source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | add target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .add v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | sub target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .sub v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | mul target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .mul v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | div target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .div v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | and target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .and v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | shiftl target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .shiftl v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | not target sourceCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_not v physicalPc target sourceCell source.mem scratch source.inp source.out
        hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | jump target =>
      simp only [Instr.effect] at heffect
      cases heffect
      exact ⟨scratch,hscratch,trivial,scratchPreservedFrom_refl 6 scratch,
        by simp [body,execute]⟩
  | jzero address target =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_jzero v physicalPc address target source.mem scratch source.inp source.out
        hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun,hready⟩
      exact ⟨nextScratch,hsNext,hready,hhigh,hrun⟩
  | jeof target =>
      simp only [Instr.effect] at heffect
      cases heffect
      exact ⟨scratch,hscratch,trivial,scratchPreservedFrom_refl 6 scratch,
        by simp [body,execute]⟩
  | inputLength address =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_inputLength v physicalPc address source.mem scratch source.inp source.out
        hcapacity hscratch with ⟨nextScratch,hsNext,hhigh,hrun⟩
      exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | inputLoad target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_inputLoad v physicalPc target addressCell source.mem scratch
        source.inp source.out hcapacity hscratch hnormal with
        ⟨nextScratch,hsNext,hhigh,hrun⟩
      refine ⟨nextScratch,hsNext,trivial,hhigh, ?_⟩
      simpa only [Nat.mod_eq_of_lt (hnormal _)] using hrun
  | halt =>
      simp only [Instr.effect] at heffect
      contradiction
  | read address =>
      simp only [Instr.effect] at heffect
      cases hinput:source.inp with
      | nil => simp [hinput] at heffect
      | cons value rest =>
          simp [hinput] at heffect
          cases heffect
          rcases body_read v physicalPc address value rest source.mem scratch source.out
            hcapacity hscratch with ⟨nextScratch,hsNext,hhigh,hrun⟩
          exact ⟨nextScratch,hsNext,trivial,hhigh,hrun⟩
  | write address =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_write v physicalPc address source.mem scratch source.inp source.out
        hcapacity hscratch hnormal with ⟨nextScratch,hsNext,hhigh,hrun⟩
      refine ⟨nextScratch,hsNext,trivial,hhigh, ?_⟩
      simpa [Nat.mod_eq_of_lt (hnormal _)] using hrun

theorem paddedBody_effect {v physicalPc:Nat} {i:Instr} {source next:State}
    {scratch:Nat→ Nat} (hcapacity:16≤ 2 ^ (v + 1))
    (hscratch:CompilerScratch v scratch) (hnormal:Normalized v source.mem)
    (heffect:i.effect v source=some next):
    ∃ nextScratch,
      CompilerScratch v nextScratch∧ BranchReady v i source nextScratch∧
      ScratchPreservedFrom 6 scratch nextScratch∧
      execute (v + 1) (paddedBody i)
        (state source.input physicalPc source.mem scratch source.inp source.out) =
        some (state next.input (physicalPc + 16) next.mem nextScratch next.inp next.out):=by
  rcases body_effect (physicalPc:=physicalPc) hcapacity hscratch hnormal heffect with
    ⟨bodyScratch,hsBody,hready,hbodyHigh,hbody⟩
  rcases padding_execute v (16 - (body i).length)
      (physicalPc + (body i).length) next.mem bodyScratch next.inp next.out
      hcapacity hsBody with ⟨nextScratch,hsNext,hfive,hpaddingHigh,hpadding⟩
  refine ⟨nextScratch,hsNext, ?_,hbodyHigh.trans hpaddingHigh, ?_⟩
  · cases i <;> simp only [BranchReady] at hready ⊢
    all_goals try trivial
    rw [hfive]
    exact hready
  · rw [paddedBody,execute_append,hbody,Option.bind_some,hpadding]
    congr 2
    have:=body_length_le i
    omega

end Lax759944Proofs.TapeRamVirtualSimulation

end

section

namespace Lax759944Proofs.TapeRamBufferedCompiler

open Lax808846.Ram TapeRamVirtualCompiler

def bufferBase:Nat:=32

def lengthRegister:Nat:=13
def cursorRegister:Nat:=15
def remainingRegister:Nat:=17
def temporaryRegister:Nat:=19
def baseRegister:Nat:=21
def oneRegister:Nat:=23
def zeroRegister:Nat:=25
def headerRegister:Nat:=27

def location (pc:Nat):Nat:=20 + 18 * pc

def initialCost (extra:Nat):Program:=TapeRamVirtualCompiler.initialCost ++
  [.set oneRegister 1,
   .set baseRegister 65,
   .set zeroRegister 0,
   .read headerRegister,
   .set lengthRegister extra,
   .add lengthRegister headerRegister lengthRegister,
   .set cursorRegister 0,
   .store baseRegister headerRegister,
   .set temporaryRegister 67,
   .sub remainingRegister lengthRegister oneRegister,
   .jzero remainingRegister (location 0),
   .read resultRegister,
   .store temporaryRegister resultRegister,
   .add temporaryRegister temporaryRegister twoRegister,
   .sub remainingRegister remainingRegister oneRegister,
   .jump 14]

def readBody (programLength target:Nat):Program:=
  [.sub resultRegister lengthRegister cursorRegister,
   .jzero resultRegister (location programLength),
   .mul addressRegister cursorRegister twoRegister,
   .add addressRegister addressRegister baseRegister,
   .load resultRegister addressRegister,
   .add cursorRegister cursorRegister oneRegister] ++ writeCell target

def inputLoadBody (pc target index:Nat):Program:=
  readCell resultRegister index ++
  [.sub temporaryRegister lengthRegister resultRegister,
   .jzero temporaryRegister (location pc + 10),
   .mul addressRegister resultRegister twoRegister,
   .add addressRegister addressRegister baseRegister,
   .load resultRegister addressRegister,
   .jump (location pc + 11),
   .set resultRegister 0] ++ writeCell target

def body (programLength pc:Nat):Instr→ Program
  | .read target => readBody programLength target
  | .inputLength target => [.add resultRegister lengthRegister zeroRegister] ++ writeCell target
  | .inputLoad target index => inputLoadBody pc target index
  | .jeof _ => [.sub resultRegister lengthRegister cursorRegister]
  | instruction => TapeRamVirtualCompiler.body instruction

def CoreInstruction:Instr→ Prop
  | .read _ | .inputLength _ | .inputLoad _ _ | .jeof _ => False
  | _ => True

theorem body_eq_of_core (programLength pc:Nat) (instruction:Instr)
    (hcore:CoreInstruction instruction):
    body programLength pc instruction=TapeRamVirtualCompiler.body instruction:=by
  cases instruction <;> simp [CoreInstruction,body] at hcore ⊢

theorem body_length_le (programLength pc:Nat) (instruction:Instr):
    (body programLength pc instruction).length≤ 16:=by
  cases instruction <;> simp [body,readBody,inputLoadBody,TapeRamVirtualCompiler.body,
    readCell,writeCell]

def paddedBody (programLength pc:Nat) (instruction:Instr):Program:=
  body programLength pc instruction ++
    List.replicate (16 - (body programLength pc instruction).length) (.set 5 0)

theorem paddedBody_eq_of_core (programLength pc:Nat) (instruction:Instr)
    (hcore:CoreInstruction instruction):
    paddedBody programLength pc instruction=TapeRamVirtualCompiler.paddedBody instruction:=by
  simp [paddedBody,TapeRamVirtualCompiler.paddedBody,
    body_eq_of_core programLength pc instruction hcore]

@[simp] theorem paddedBody_length (programLength pc:Nat) (instruction:Instr):
    (paddedBody programLength pc instruction).length=16:=by
  simp only [paddedBody,List.length_append,List.length_replicate]
  have:=body_length_le programLength pc instruction
  omega

def branch (pc:Nat):Instr→ Program
  | .halt => [.halt, .halt]
  | .jump target => [.jump (location target), .halt]
  | .jzero _ target | .jeof target =>
      [.jzero resultRegister (location target), .jump (location (pc + 1))]
  | _ => [.jump (location (pc + 1)), .halt]

def block (programLength pc:Nat) (instruction:Instr):Program:=
  paddedBody programLength pc instruction ++ branch pc instruction

def blocks (programLength pc:Nat):Program→ Program
  | [] => []
  | instruction::rest =>
      block programLength pc instruction ++ blocks programLength (pc + 1) rest

def compile (extra:Nat) (program:Program):Program:=
  initialCost extra ++ blocks program.length 0 program ++ [.halt]

@[simp] theorem prelude_length (extra:Nat):(initialCost extra).length=20:=by rfl

@[simp] theorem branch_length (pc:Nat) (instruction:Instr):
    (branch pc instruction).length=2:=by cases instruction <;> rfl

@[simp] theorem block_length (programLength pc:Nat) (instruction:Instr):
    (block programLength pc instruction).length=18:=by simp [block]

@[simp] theorem blocks_length (programLength pc:Nat) (program:Program):
    (blocks programLength pc program).length=18 * program.length:=by
  induction program generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [blocks,List.length_append,block_length,ih,List.length_cons]
      omega

@[simp] theorem compile_length (extra:Nat) (program:Program):
    (compile extra program).length=location program.length + 1:=by
  simp [compile,location,Nat.add_assoc]

theorem blocks_get (program:Program) (programLength base pc offset:Nat)
    (hoffset:offset < 18):
    (blocks programLength base program)[18 * pc + offset]? =
      program[pc]?.bind (fun instruction =>
        (block programLength (base + pc) instruction)[offset]?):=by
  induction program generalizing base pc with
  | nil => simp [blocks]
  | cons instruction rest ih =>
      cases pc with
      | zero => simp [blocks,List.getElem?_append,hoffset]
      | succ pc =>
          have hlarge:¬18 * (pc + 1) + offset < 18:=by omega
          simp only [blocks,List.getElem?_append,block_length,hlarge,
            ↓reduceIte,List.getElem?_cons_succ]
          rw [show 18 * (pc + 1) + offset - 18=18 * pc + offset by omega,ih]
          simp [Nat.add_comm,Nat.add_left_comm]

theorem compile_get (extra:Nat) (program:Program) (pc offset:Nat)
    (hpc:pc < program.length) (hoffset:offset < 18):
    (compile extra program)[location pc + offset]? =
      program[pc]?.bind (fun instruction =>
        (block program.length pc instruction)[offset]?):=by
  have hprefix:location pc + offset < (initialCost extra ++ blocks program.length 0 program).length:=by
    simp only [List.length_append,prelude_length,blocks_length,location]
    omega
  have hlarge:¬location pc + offset < (initialCost extra).length:=by
    simp only [prelude_length,location]
    omega
  simp only [compile,List.getElem?_append,hprefix,hlarge, ↓reduceIte]
  have hsub:location pc + offset - (initialCost extra).length=18 * pc + offset:=by
    simp only [prelude_length,location]
    omega
  rw [hsub,blocks_get program program.length 0 pc offset hoffset,Nat.zero_add]

theorem compile_get_paddedBody (extra:Nat) (program:Program) (pc:Nat)
    (instruction:Instr) (hfetch:program[pc]?=some instruction)
    (offset:Nat) (hoffset:offset < 16):
    (compile extra program)[location pc + offset]? =
      (paddedBody program.length pc instruction)[offset]?:=by
  have hpc:=(List.getElem?_eq_some_iff.mp hfetch).choose
  rw [compile_get extra program pc offset hpc (by omega),hfetch]
  simp [block,List.getElem?_append,hoffset]

theorem compile_get_branch (extra:Nat) (program:Program) (pc:Nat)
    (instruction:Instr) (hfetch:program[pc]?=some instruction)
    (offset:Nat) (hoffset:offset < 2):
    (compile extra program)[location pc + 16 + offset]? =
      (branch pc instruction)[offset]?:=by
  have hpc:=(List.getElem?_eq_some_iff.mp hfetch).choose
  rw [show location pc + 16 + offset=location pc + (16 + offset) by omega,
    compile_get extra program pc (16 + offset) hpc (by omega),hfetch]
  simp [block,List.getElem?_append,hoffset]

@[simp] theorem compile_get_halt (extra:Nat) (program:Program):
    (compile extra program)[location program.length]?=some .halt:=by
  simp [compile,List.getElem?_append,location]

theorem compile_get_outside (extra:Nat) (program:Program) (pc:Nat)
    (hpc:program.length < pc):
    (compile extra program)[location pc]?=none:=by
  apply List.getElem?_eq_none
  simp only [compile_length,location]
  omega

end Lax759944Proofs.TapeRamBufferedCompiler

end

section

namespace Lax759944Proofs.TapeRamBufferedState

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler

def BufferStored (values:List Nat) (scratch:Nat→ Nat):Prop:=
  ∀ (index:Nat) (hindex:index < values.length),
    scratch (bufferBase + index)=values[index]'hindex

structure AdapterScratch (v:Nat) (values:List Nat) (cursor:Nat)
    (scratch:Nat→ Nat):Prop where
  compiler:CompilerScratch v scratch
  length_eq:scratch 6=values.length
  cursor_eq:scratch 7=cursor
  base_eq:scratch 10=65
  one_eq:scratch 11=1
  zero_eq:scratch 12=0
  cursor_le:cursor≤ values.length
  buffer:BufferStored values scratch

theorem BufferStored.preserve {values:List Nat} {before after:Nat→ Nat}
    (hbefore:BufferStored values before)
    (hhigh:ScratchPreservedFrom 32 before after):BufferStored values after:=by
  intro index hindex
  rw [hhigh (bufferBase + index) (by simp [bufferBase])]
  exact hbefore index hindex

theorem AdapterScratch.preserve {v:Nat} {values:List Nat} {cursor:Nat}
    {before after:Nat→ Nat} (hbefore:AdapterScratch v values cursor before)
    (hcompiler:CompilerScratch v after)
    (hhigh:ScratchPreservedFrom 6 before after):AdapterScratch v values cursor after:=by
  refine ⟨hcompiler, ?_, ?_, ?_, ?_, ?_,hbefore.cursor_le, ?_⟩
  · rw [hhigh 6 (by omega)]; exact hbefore.length_eq
  · rw [hhigh 7 (by omega)]; exact hbefore.cursor_eq
  · rw [hhigh 10 (by omega)]; exact hbefore.base_eq
  · rw [hhigh 11 (by omega)]; exact hbefore.one_eq
  · rw [hhigh 12 (by omega)]; exact hbefore.zero_eq
  · apply hbefore.buffer.preserve
    intro index hindex
    exact hhigh index (by omega)

theorem buffer_address_lt {v:Nat} {values:List Nat} {index:Nat}
    (hcapacity:values.length + 32 < 2 ^ v) (hindex:index < values.length):
    65 + 2 * index < 2 ^ (v + 1):=by
  rw [Nat.pow_succ]
  omega

theorem length_lt {v:Nat} {values:List Nat}
    (hcapacity:values.length + 32 < 2 ^ v):values.length < 2 ^ v:=by omega

def BranchReady (v:Nat) (instruction:Instr) (source:State)
    (scratch:Nat→ Nat):Prop:=
  match instruction with
  | .jzero address _ => scratch 5=source.mem (address % 2 ^ v)
  | .jeof _ => (scratch 5=0↔ source.inp=[])
  | _ => True

def Simulates (v:Nat) (values:List Nat) (source physical:State):Prop:=
  ∃ cursor scratch,
    source.input=values∧ source.inp=values.drop cursor∧
    Normalized v source.mem∧ AdapterScratch v values cursor scratch∧
    physical=state values (location source.pc) source.mem scratch [] source.out

end Lax759944Proofs.TapeRamBufferedState

end

section

namespace Lax759944Proofs.TapeRamBufferedInputs

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler TapeRamBufferedState

theorem large_capacity {v:Nat} {values:List Nat}
    (hcapacity:values.length + 32 < 2 ^ v):64 < 2 ^ (v + 1):=by
  rw [Nat.pow_succ]
  omega

theorem pad_run {v extra cursor:Nat} {values:List Nat} {program:Program}
    {instruction:Instr} {source next:State} {before bodyScratch:Nat→ Nat}
    (hcapacity:16≤ 2 ^ (v + 1)) (hfetch:program[source.pc]?=some instruction)
    (hadapter:AdapterScratch v values cursor bodyScratch)
    (hready:BranchReady v instruction source bodyScratch)
    (hlinear:∀ i∈ body program.length source.pc instruction,StraightLine i)
    (hbody:execute (v + 1) (body program.length source.pc instruction)
      (state values (location source.pc) source.mem before [] source.out) =
        some (state values (location source.pc + (body program.length source.pc instruction).length)
          next.mem bodyScratch [] next.out)):
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch∧ BranchReady v instruction source nextScratch∧
      run (v + 1) (compile extra program) 16
        (state values (location source.pc) source.mem before [] source.out) =
        some (state values (location source.pc + 16) next.mem nextScratch [] next.out):=by
  rcases padding_execute v (16 - (body program.length source.pc instruction).length)
      (location source.pc + (body program.length source.pc instruction).length)
      next.mem bodyScratch [] next.out hcapacity hadapter.compiler with
    ⟨nextScratch,hcompiler,hfive,hhigh,hpadding⟩
  refine ⟨nextScratch,hadapter.preserve hcompiler hhigh, ?_, ?_⟩
  · cases instruction <;> simp only [BranchReady] at hready ⊢
    all_goals try trivial
    all_goals rw [hfive]; exact hready
  · have hall:∀ i∈ paddedBody program.length source.pc instruction,StraightLine i:=by
      intro i hi
      simp only [paddedBody,List.mem_append,List.mem_replicate] at hi
      rcases hi with hi | ⟨_,rfl⟩
      · exact hlinear i hi
      · trivial
    have hprefix:∀ k,k < (paddedBody program.length source.pc instruction).length→
        (compile extra program)[(state values (location source.pc) source.mem before [] source.out).pc + k]? =
          (paddedBody program.length source.pc instruction)[k]?:=by
      intro k hk
      exact compile_get_paddedBody extra program source.pc instruction hfetch k (by simpa using hk)
    rw [show 16=(paddedBody program.length source.pc instruction).length by simp,
      run_eq_execute _ _ _ _ hall hprefix,paddedBody,execute_append,hbody,
      Option.bind_some,hpadding]
    congr 2
    simp only [List.length_append,List.length_replicate]
    have:=body_length_le program.length source.pc instruction
    omega

theorem inputLength_body {v pc cursor programLength address:Nat} {values:List Nat}
    {memory scratch:Nat→ Nat} {output:List Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hscratch:AdapterScratch v values cursor scratch):
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch∧
      execute (v + 1) (body programLength pc (.inputLength address))
        (state values pc memory scratch [] output) =
        some (state values (pc + 6) (setCell v memory address values.length)
          nextScratch [] output):=by
  have hlarge:=large_capacity hcapacity
  rcases TapeRamVirtualSimulation.body_set (original:=values) v pc address values.length
      memory scratch [] output (by omega) hscratch.compiler with
    ⟨nextScratch,hcompiler,hhigh,hbody⟩
  refine ⟨nextScratch,hscratch.preserve hcompiler hhigh, ?_⟩
  have h13:13 % 2 ^ (v + 1)=13:=Nat.mod_eq_of_lt (by omega)
  have h25:25 % 2 ^ (v + 1)=25:=Nat.mod_eq_of_lt (by omega)
  have hlength:merge memory scratch 13=values.length:=by
    simpa only [hscratch.length_eq] using merge_odd memory scratch 6
  have hzero:merge memory scratch 25=0:=by
    simpa only [hscratch.zero_eq] using merge_odd memory scratch 12
  have hlen:(TapeRamVirtualCompiler.body (.set address values.length)).length=6:=rfl
  rw [hlen] at hbody
  simpa only [body,TapeRamVirtualCompiler.body,List.singleton_append,execute,
    Instr.effect,state,lengthRegister,zeroRegister,TapeRamVirtualCompiler.resultRegister,
    h13,h25,hlength,hzero,Nat.add_zero] using hbody

theorem inputLength_run {v extra cursor address:Nat} {values:List Nat} {program:Program}
    {source:State} {scratch:Nat→ Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfetch:program[source.pc]?=some (.inputLength address))
    (hscratch:AdapterScratch v values cursor scratch):
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch∧
      run (v + 1) (compile extra program) 16
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16)
          (setCell v source.mem address values.length) nextScratch [] source.out):=by
  rcases inputLength_body (pc:=location source.pc) (programLength:=program.length)
      (address:=address) (memory:=source.mem) (output:=source.out) hcapacity hscratch with
    ⟨bodyScratch,hadapter,hbody⟩
  let next:State:= { source with mem:=setCell v source.mem address values.length }
  have hlarge:=large_capacity hcapacity
  rcases pad_run (extra:=extra) (next:=next) (by omega) hfetch hadapter
      (by trivial) (by simp [body,TapeRamVirtualCompiler.writeCell,StraightLine])
      (by simpa [next,body,TapeRamVirtualCompiler.writeCell] using hbody) with
    ⟨nextScratch,hnext,_,hrun⟩
  exact ⟨nextScratch,hnext,hrun⟩

theorem jeof_run {v extra cursor target:Nat} {values:List Nat} {program:Program}
    {source:State} {scratch:Nat→ Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfetch:program[source.pc]?=some (.jeof target))
    (hinput:source.inp=values.drop cursor)
    (hscratch:AdapterScratch v values cursor scratch):
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch∧
      BranchReady v (.jeof target) source nextScratch∧
      run (v + 1) (compile extra program) 16
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16) source.mem nextScratch [] source.out):=by
  have hlarge:=large_capacity hcapacity
  have hgap:values.length - cursor < 2 ^ (v + 1):=by
    have:=length_lt hcapacity
    have:=Nat.pow_le_pow_right (by decide:1≤ 2) (show v≤ v + 1 by omega)
    omega
  let after:=put scratch 5 (values.length - cursor)
  have hafter:AdapterScratch v values cursor after:=hscratch.preserve
    (compilerScratch_put v scratch hscratch.compiler 5 _ (by omega))
    (scratchPreservedFrom_put 6 scratch 5 _ (by omega))
  have hready:BranchReady v (.jeof target) source after:=by
    simp [BranchReady,after,hinput,Nat.sub_eq_zero_iff_le,List.drop_eq_nil_iff]
  have hbody:execute (v + 1) (body program.length source.pc (.jeof target))
      (state values (location source.pc) source.mem scratch [] source.out) =
      some (state values (location source.pc + 1) source.mem after [] source.out):=by
    simpa only [body,TapeRamVirtualCompiler.resultRegister,lengthRegister,
      cursorRegister,BinaryKind.instruction,BinaryKind.value,hscratch.length_eq,
      hscratch.cursor_eq,Nat.mod_eq_of_lt hgap] using
      (binaryRegister_execute (original:=values) .sub v (location source.pc) 5 6 7
        source.mem scratch [] source.out (by omega) (by omega) (by omega))
  exact pad_run (extra:=extra) (next:=source) (by omega) hfetch hafter hready
    (by simp [body,StraightLine]) (by simpa [body] using hbody)

end Lax759944Proofs.TapeRamBufferedInputs

end

section

namespace Lax759944Proofs.TapeRamBufferedRead

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler TapeRamBufferedState TapeRamBufferedInputs

theorem run_one_of_execute {w:Nat} {program:Program} {instruction:Instr}
    {source next:State} (hfetch:program[source.pc]?=some instruction)
    (heffect:execute w [instruction] source=some next):
    run w program 1 source=some next:=by
  simpa only [run,step,hfetch,Option.bind_some,execute,Option.bind_fun_some] using heffect

theorem read_prefix {v extra cursor address:Nat} {values:List Nat} {program:Program}
    {pc:Nat} {memory scratch:Nat→ Nat} {output:List Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfit:∀ value∈ values,value < 2 ^ v)
    (hfetch:program[pc]?=some (.read address))
    (hscratch:AdapterScratch v values cursor scratch) (hcursor:cursor < values.length):
    ∃ nextScratch,
      AdapterScratch v values (cursor + 1) nextScratch∧
      nextScratch 5=values[cursor]'hcursor∧
      run (v + 1) (compile extra program) 6
        (state values (location pc) memory scratch [] output) =
        some (state values (location pc + 6) memory nextScratch [] output):=by
  let gap:=values.length - cursor
  let value:=values[cursor]'hcursor
  let s1:=put scratch 5 gap
  let s3:=put s1 2 (2 * cursor)
  let s4:=put s3 2 (65 + 2 * cursor)
  let s5:=put s4 5 value
  let s6:=put s5 7 (cursor + 1)
  have hlarge:=large_capacity hcapacity
  have hgap:gap < 2 ^ (v + 1):=by
    dsimp [gap]
    have:=length_lt hcapacity
    have:=Nat.pow_le_pow_right (by decide:1≤ 2) (show v≤ v + 1 by omega)
    omega
  have hgapZero:gap ≠ 0:=by dsimp [gap]; omega
  have hdouble:2 * cursor < 2 ^ (v + 1):=by rw [Nat.pow_succ]; omega
  have haddress:=buffer_address_lt hcapacity hcursor
  have hsum:2 * cursor + 65 < 2 ^ (v + 1):=by omega
  have hnextCursor:cursor + 1 < 2 ^ (v + 1):=by
    have:=length_lt hcapacity
    have:=Nat.pow_le_pow_right (by decide:1≤ 2) (show v≤ v + 1 by omega)
    omega
  have hvalue:value < 2 ^ v:=hfit value (List.getElem_mem hcursor)
  have hvaluePhysical:value < 2 ^ (v + 1):=
    hvalue.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have h13:13 % 2 ^ (v + 1)=13:=Nat.mod_eq_of_lt (by omega)
  have h15:15 % 2 ^ (v + 1)=15:=Nat.mod_eq_of_lt (by omega)
  have h11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
  have h5:5 % 2 ^ (v + 1)=5:=Nat.mod_eq_of_lt (by omega)
  have hf0:(compile extra program)[location pc + 0]?=some (.sub 11 13 15):=by
    simpa [paddedBody,body,readBody,TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister,lengthRegister,cursorRegister,
      baseRegister,oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 0 (by omega)
  have hf1:(compile extra program)[location pc + 1]?=some (.jzero 11 (location program.length)):=by
    simpa [paddedBody,body,readBody,TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister,lengthRegister,cursorRegister,
      baseRegister,oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 1 (by omega)
  have hf2:(compile extra program)[location pc + 2]?=some (.mul 5 15 3):=by
    simpa [paddedBody,body,readBody,TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister,lengthRegister,cursorRegister,
      baseRegister,oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 2 (by omega)
  have hf3:(compile extra program)[location pc + 3]?=some (.add 5 5 21):=by
    simpa [paddedBody,body,readBody,TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister,lengthRegister,cursorRegister,
      baseRegister,oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 3 (by omega)
  have hf4:(compile extra program)[location pc + 4]?=some (.load 11 5):=by
    simpa [paddedBody,body,readBody,TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister,lengthRegister,cursorRegister,
      baseRegister,oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 4 (by omega)
  have hf5:(compile extra program)[location pc + 5]?=some (.add 15 15 23):=by
    simpa [paddedBody,body,readBody,TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister,lengthRegister,cursorRegister,
      baseRegister,oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 5 (by omega)
  have h0:execute (v + 1) [.sub 11 13 15]
      (state values (location pc) memory scratch [] output) =
      some (state values (location pc + 1) memory s1 [] output):=by
    have hsub:=binaryRegister_execute (original:=values) .sub v (location pc) 5 6 7
      memory scratch [] output (by omega) (by omega) (by omega)
    simp only [BinaryKind.instruction,BinaryKind.value,hscratch.length_eq,
      hscratch.cursor_eq] at hsub
    rw [Nat.mod_eq_of_lt (show values.length - cursor < 2 ^ (v + 1) from hgap)] at hsub
    exact hsub
  have h1:execute (v + 1) [.jzero 11 (location program.length)]
      (state values (location pc + 1) memory s1 [] output) =
      some (state values (location pc + 2) memory s1 [] output):=by
    have hread:merge memory s1 11=gap:=by simpa [s1] using merge_odd memory s1 5
    simp [execute,Instr.effect,state,h11,hread,hgapZero]
  have h2:execute (v + 1) [.mul 5 15 3]
      (state values (location pc + 2) memory s1 [] output) =
      some (state values (location pc + 3) memory s3 [] output):=by
    have hmul:=binaryRegister_execute (original:=values) .mul v (location pc + 2) 2 7 1
      memory s1 [] output (by omega) (by omega) (by omega)
    simp only [BinaryKind.instruction,BinaryKind.value] at hmul
    rw [show s1 7=cursor by simp [s1,put,hscratch.cursor_eq],
      show s1 1=2 by simp [s1,put,hscratch.compiler.2],
      Nat.mul_comm cursor 2,Nat.mod_eq_of_lt hdouble] at hmul
    exact hmul
  have h3:execute (v + 1) [.add 5 5 21]
      (state values (location pc + 3) memory s3 [] output) =
      some (state values (location pc + 4) memory s4 [] output):=by
    have hadd:=binaryRegister_execute (original:=values) .add v (location pc + 3) 2 2 10
      memory s3 [] output (by omega) (by omega) (by omega)
    simp only [BinaryKind.instruction,BinaryKind.value] at hadd
    rw [show s3 2=2 * cursor by simp [s3],
      show s3 10=65 by simp [s3,s1,put,hscratch.base_eq],
      Nat.mod_eq_of_lt hsum,Nat.add_comm (2 * cursor) 65] at hadd
    exact hadd
  have h4:execute (v + 1) [.load 11 5]
      (state values (location pc + 4) memory s4 [] output) =
      some (state values (location pc + 5) memory s5 [] output):=by
    have hpointer:merge memory s4 5=65 + 2 * cursor:=by
      simpa [s4] using merge_odd memory s4 2
    have hbuffer:merge memory s4 (65 + 2 * cursor)=value:=by
      rw [show 65 + 2 * cursor=2 * (bufferBase + cursor) + 1 by simp [bufferBase]; omega,
        merge_odd]
      simpa [s4,s3,s1,put,bufferBase,value,
        show 32 + cursor ≠ 2 by omega,show 32 + cursor ≠ 5 by omega] using
        hscratch.buffer cursor hcursor
    have hset:=set_odd v memory s4 11 value (by decide) (by omega)
    simp only [execute,Instr.effect,state,h5,hpointer,
      Nat.mod_eq_of_lt haddress,hbuffer,hset,Option.bind_some]
    simpa [s5,Nat.mod_eq_of_lt hvaluePhysical]
  have h5run:execute (v + 1) [.add 15 15 23]
      (state values (location pc + 5) memory s5 [] output) =
      some (state values (location pc + 6) memory s6 [] output):=by
    simpa [BinaryKind.instruction,BinaryKind.value,s1,s3,s4,s5,s6,put,
      hscratch.cursor_eq,hscratch.one_eq,Nat.mod_eq_of_lt hnextCursor] using
      (binaryRegister_execute (original:=values) .add v (location pc + 5) 7 7 11
        memory s5 [] output (by omega) (by omega) (by omega))
  have hsix:AdapterScratch v values (cursor + 1) s6:=by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_,by omega, ?_⟩
    · constructor <;> simp [s6,s5,s4,s3,s1,put,hscratch.compiler.1,hscratch.compiler.2]
    · simp [s6,s5,s4,s3,s1,put,hscratch.length_eq]
    · simp [s6,put]
    · simp [s6,s5,s4,s3,s1,put,hscratch.base_eq]
    · simp [s6,s5,s4,s3,s1,put,hscratch.one_eq]
    · simp [s6,s5,s4,s3,s1,put,hscratch.zero_eq]
    · apply hscratch.buffer.preserve
      intro index hindex
      simp [s6,s5,s4,s3,s1,put,show index ≠ 7 by omega,
        show index ≠ 5 by omega,show index ≠ 2 by omega]
  refine ⟨s6,hsix,by simp [s6,s5,put,value], ?_⟩
  have hr0:=run_one_of_execute (by simpa only [state,Nat.add_zero] using hf0) h0
  have hr1:=run_one_of_execute (by simpa only [state] using hf1) h1
  have hr2:=run_one_of_execute (by simpa only [state] using hf2) h2
  have hr3:=run_one_of_execute (by simpa only [state] using hf3) h3
  have hr4:=run_one_of_execute (by simpa only [state] using hf4) h4
  have hr5:=run_one_of_execute (by simpa only [state] using hf5) h5run
  rw [show 6=1 + (1 + (1 + (1 + (1 + 1)))) by decide,
    run_add,hr0,Option.bind_some,run_add,hr1,Option.bind_some,
    run_add,hr2,Option.bind_some,run_add,hr3,Option.bind_some,
    run_add,hr4,Option.bind_some,hr5]

theorem read_run {v extra cursor address:Nat} {values:List Nat} {program:Program}
    {pc:Nat} {memory scratch:Nat→ Nat} {output:List Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfit:∀ value∈ values,value < 2 ^ v)
    (hfetch:program[pc]?=some (.read address))
    (hscratch:AdapterScratch v values cursor scratch) (hcursor:cursor < values.length):
    ∃ nextScratch,
      AdapterScratch v values (cursor + 1) nextScratch∧
      run (v + 1) (compile extra program) 16
        (state values (location pc) memory scratch [] output) =
        some (state values (location pc + 16)
          (setCell v memory address (values[cursor]'hcursor)) nextScratch [] output):=by
  rcases read_prefix (extra:=extra) (memory:=memory) (output:=output) hcapacity hfit hfetch hscratch hcursor with
    ⟨prefixScratch,hprefixAdapter,hvalue,hprefixRun⟩
  let value:=values[cursor]'hcursor
  let afterWrite:=put (put prefixScratch 2 (2 * (address % 2 ^ v))) 5 value
  have hword:value < 2 ^ v:=hfit value (List.getElem_mem hcursor)
  have hlarge:=large_capacity hcapacity
  have hwriteCompiler:CompilerScratch v afterWrite:=compilerScratch_put v _
    (compilerScratch_put v prefixScratch hprefixAdapter.compiler 2 _ (by omega)) 5 _ (by omega)
  have hwriteAdapter:AdapterScratch v values (cursor + 1) afterWrite:=
    hprefixAdapter.preserve hwriteCompiler (by
      intro index hindex
      simp [afterWrite,put,show index ≠ 2 by omega,show index ≠ 5 by omega])
  rcases padding_execute (original:=values) v 5 (location pc + 11)
      (setCell v memory address value) afterWrite [] output (by omega) hwriteCompiler with
    ⟨nextScratch,hnextCompiler,_,hnextHigh,hpadding⟩
  refine ⟨nextScratch,hwriteAdapter.preserve hnextCompiler hnextHigh, ?_⟩
  let suffix:Program:=TapeRamVirtualCompiler.writeCell address ++ List.replicate 5 (.set 5 0)
  let prefixCode:Program:=
    [.sub 11 13 15, .jzero 11 (location program.length), .mul 5 15 3,
      .add 5 5 21, .load 11 5, .add 15 15 23]
  have hdecomp:paddedBody program.length pc (.read address)=prefixCode ++ suffix:=by rfl
  have hprefixLength:prefixCode.length=6:=rfl
  have hsuffixLength:suffix.length=10:=rfl
  have hlinear:∀ i∈ suffix,StraightLine i:=by
    simp [suffix,TapeRamVirtualCompiler.writeCell,StraightLine]
  have hsuffixFetch:∀ k,k < suffix.length→
      (compile extra program)[(state values (location pc + 6) memory prefixScratch [] output).pc + k]? =
        suffix[k]?:=by
    intro k hk
    change (compile extra program)[location pc + 6 + k]?=_
    rw [show location pc + 6 + k=location pc + (6 + k) by omega,
      compile_get_paddedBody extra program pc (.read address) hfetch (6 + k)
        (by rw [hsuffixLength] at hk; omega),hdecomp]
    simp [List.getElem?_append,hprefixLength,show ¬6 + k < 6 by omega]
  have hsuffixExecute:execute (v + 1) suffix
      (state values (location pc + 6) memory prefixScratch [] output) =
      some (state values (location pc + 16) (setCell v memory address value) nextScratch [] output):=by
    simp only [suffix]
    rw [execute_append,writeCell_execute v (location pc + 6) address
      memory prefixScratch [] output (by omega) hprefixAdapter.compiler.1 hprefixAdapter.compiler.2]
    simp only [Option.bind_some,hvalue,
      Nat.mod_eq_of_lt (show values[cursor] < 2 ^ v from hword)]
    exact hpadding
  have hsuffixRun:run (v + 1) (compile extra program) 10
      (state values (location pc + 6) memory prefixScratch [] output) =
      some (state values (location pc + 16) (setCell v memory address value) nextScratch [] output):=by
    rw [← hsuffixLength,run_eq_execute _ _ _ _ hlinear hsuffixFetch]
    exact hsuffixExecute
  rw [show 16=6 + 10 by decide,run_add,hprefixRun,Option.bind_some,hsuffixRun]

theorem read_exhausted {v extra address:Nat} {values:List Nat} {program:Program}
    {pc:Nat} {memory scratch:Nat→ Nat} {output:List Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfetch:program[pc]?=some (.read address))
    (hscratch:AdapterScratch v values values.length scratch):
    ∃ final,
      run (v + 1) (compile extra program) 2
        (state values (location pc) memory scratch [] output)=some final∧
      step (v + 1) (compile extra program) final=none∧ final.out=output:=by
  have hlarge:=large_capacity hcapacity
  let after:=put scratch 5 0
  have hsub:execute (v + 1) [.sub 11 13 15]
      (state values (location pc) memory scratch [] output) =
      some (state values (location pc + 1) memory after [] output):=by
    simpa [BinaryKind.instruction,BinaryKind.value,hscratch.length_eq,hscratch.cursor_eq,after] using
      (binaryRegister_execute (original:=values) .sub v (location pc) 5 6 7
        memory scratch [] output (by omega) (by omega) (by omega))
  have hbranch:execute (v + 1) [.jzero 11 (location program.length)]
      (state values (location pc + 1) memory after [] output) =
      some (state values (location program.length) memory after [] output):=by
    have h11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
    have hzero:merge memory after 11=0:=by simpa [after] using merge_odd memory after 5
    simp [execute,Instr.effect,state,h11,hzero]
  have hf0:(compile extra program)[location pc]?=some (.sub 11 13 15):=by
    simpa [paddedBody,body,readBody,TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister,lengthRegister,cursorRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 0 (by omega)
  have hf1:(compile extra program)[location pc + 1]? =
      some (.jzero 11 (location program.length)):=by
    simpa [paddedBody,body,readBody,TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 1 (by omega)
  refine ⟨state values (location program.length) memory after [] output, ?_, ?_,rfl⟩
  · have hr0:=run_one_of_execute (by simpa only [state] using hf0) hsub
    have hr1:=run_one_of_execute (by simpa only [state] using hf1) hbranch
    rw [show 2=1 + 1 by decide,run_add,hr0,Option.bind_some,hr1]
  · simp only [step,state,compile_get_halt,Option.bind_some,Instr.effect]

end Lax759944Proofs.TapeRamBufferedRead

end

section

namespace Lax759944Proofs.TapeRamBufferedIndexed

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler TapeRamBufferedState

private theorem put_low {v cursor:Nat} {values:List Nat} {scratch:Nat→ Nat}
    (h:AdapterScratch v values cursor scratch) (i value:Nat)
    (hi:2≤ i) (hi':i < 6):AdapterScratch v values cursor (put scratch i value):=
  h.preserve (compilerScratch_put v scratch h.compiler i value hi)
    (scratchPreservedFrom_put 6 scratch i value hi')

private theorem put_temporary {v cursor:Nat} {values:List Nat} {scratch:Nat→ Nat}
    (h:AdapterScratch v values cursor scratch) (value:Nat):
    AdapterScratch v values cursor (put scratch 9 value):=by
  refine ⟨compilerScratch_put v scratch h.compiler 9 value (by omega),
    ?_, ?_, ?_, ?_, ?_,h.cursor_le, ?_⟩
  · simpa using h.length_eq
  · simpa using h.cursor_eq
  · simpa using h.base_eq
  · simpa using h.one_eq
  · simpa using h.zero_eq
  · exact h.buffer.preserve (scratchPreservedFrom_put 32 scratch 9 value (by omega))

theorem inputLoad_fetch {extra pc address index offset:Nat} {program:Program}
    (hfetch:program[pc]?=some (.inputLoad address index)) (hoffset:offset < 16):
    (compile extra program)[location pc + offset]? =
      (inputLoadBody pc address index)[offset]?:=by
  rw [compile_get_paddedBody extra program pc (.inputLoad address index) hfetch offset hoffset]
  simp [paddedBody,body,inputLoadBody,TapeRamVirtualCompiler.readCell,
    TapeRamVirtualCompiler.writeCell]

theorem inputLoad_head {v extra cursor address index:Nat} {values:List Nat}
    {program:Program} {source:State} {scratch:Nat→ Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfetch:program[source.pc]?=some (.inputLoad address index))
    (hnormal:Normalized v source.mem) (hscratch:AdapterScratch v values cursor scratch):
    let offset:=source.mem (index % 2 ^ v)
    let after:=put (put (put scratch 2 (2 * (index % 2 ^ v))) 5 offset)
      9 (values.length - offset)
    AdapterScratch v values cursor after∧
      run (v + 1) (compile extra program) 5
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 5) source.mem after [] source.out):=by
  dsimp only
  let offset:=source.mem (index % 2 ^ v)
  let loaded:=put (put scratch 2 (2 * (index % 2 ^ v))) 5 offset
  let after:=put loaded 9 (values.length - offset)
  have hlarge:64 < 2 ^ (v + 1):=by rw [Nat.pow_succ]; omega
  have hloaded:AdapterScratch v values cursor loaded:=
    put_low (put_low hscratch 2 _ (by omega) (by omega)) 5 _ (by omega) (by omega)
  refine ⟨put_temporary hloaded _, ?_⟩
  let code:=TapeRamVirtualCompiler.readCell 11 index ++ [.sub 19 13 11]
  have hcode:code.length=5:=rfl
  have hlinear:∀ i∈ code,StraightLine i:=by
    simp [code,TapeRamVirtualCompiler.readCell,StraightLine]
  have hprefix:∀ k,k < code.length→
      (compile extra program)[(state values (location source.pc) source.mem scratch [] source.out).pc + k]? =
        code[k]?:=by
    intro k hk
    have hk':k < 5:=by simpa [hcode] using hk
    change (compile extra program)[location source.pc + k]?=code[k]?
    rw [inputLoad_fetch hfetch (by omega)]
    interval_cases k <;> simp [code,inputLoadBody,TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,TapeRamVirtualCompiler.twoRegister,temporaryRegister,lengthRegister,baseRegister]
  rw [← hcode,run_eq_execute _ _ _ _ hlinear hprefix]
  dsimp only [code]
  rw [execute_append]
  rw [readCell_execute v (location source.pc) index 5 source.mem scratch [] source.out
    (by omega) (by omega) hscratch.compiler.1 hscratch.compiler.2 hnormal]
  simp only [Option.bind_some]
  have hgap:values.length - offset < 2 ^ (v + 1):=by
    rw [Nat.pow_succ]
    omega
  have hsub:=binaryRegister_execute (original:=values) .sub v (location source.pc + 4)
    9 6 5 source.mem loaded [] source.out (by omega) (by omega) (by omega)
  simpa [loaded,after,offset,BinaryKind.instruction,BinaryKind.value,
    hscratch.length_eq,Nat.mod_eq_of_lt hgap,Nat.add_assoc,TapeRamVirtualCompiler.readCell] using hsub

theorem inputLoad_write {v extra cursor address index:Nat} {values:List Nat}
    {program:Program} {source:State} {scratch:Nat→ Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfetch:program[source.pc]?=some (.inputLoad address index))
    (hscratch:AdapterScratch v values cursor scratch):
    ∃ nextScratch,AdapterScratch v values cursor nextScratch∧
      run (v + 1) (compile extra program) 5
        (state values (location source.pc + 11) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16)
          (setCell v source.mem address (scratch 5)) nextScratch [] source.out):=by
  have hlarge:64 < 2 ^ (v + 1):=by rw [Nat.pow_succ]; omega
  let next:=put (put scratch 2 (2 * (address % 2 ^ v))) 5 (scratch 5 % 2 ^ v)
  refine ⟨next,put_low (put_low hscratch 2 _ (by omega) (by omega))
    5 _ (by omega) (by omega), ?_⟩
  have hlinear:∀ i∈ TapeRamVirtualCompiler.writeCell address,StraightLine i:=by
    simp [TapeRamVirtualCompiler.writeCell,StraightLine]
  have hprefix:∀ k,k < (TapeRamVirtualCompiler.writeCell address).length→
      (compile extra program)[(state values (location source.pc + 11) source.mem scratch [] source.out).pc + k]? =
        (TapeRamVirtualCompiler.writeCell address)[k]?:=by
    intro k hk
    have hk':k < 5:=hk
    change (compile extra program)[location source.pc + 11 + k]?=_
    rw [Nat.add_assoc,inputLoad_fetch hfetch (by omega)]
    interval_cases k <;> simp [inputLoadBody,TapeRamVirtualCompiler.readCell,
      TapeRamVirtualCompiler.writeCell]
  change run (v + 1) (compile extra program) (TapeRamVirtualCompiler.writeCell address).length _=_
  rw [run_eq_execute _ _ _ _ hlinear hprefix]
  simpa [next,Nat.add_assoc] using writeCell_execute (original:=values)
    v (location source.pc + 11) address source.mem scratch [] source.out
    (by omega) hscratch.compiler.1 hscratch.compiler.2

theorem inputLoad_hit {v extra cursor address index offset:Nat} {values:List Nat}
    {program:Program} {source:State} {scratch:Nat→ Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfetch:program[source.pc]?=some (.inputLoad address index))
    (hscratch:AdapterScratch v values cursor scratch)
    (hindex:scratch 5=offset) (hgap:scratch 9=values.length - offset)
    (hhit:offset < values.length):
    ∃ after,AdapterScratch v values cursor after∧
      after 5=(values[offset]'hhit) % 2 ^ (v + 1)∧
      run (v + 1) (compile extra program) 5
        (state values (location source.pc + 5) source.mem scratch [] source.out) =
        some (state values (location source.pc + 11) source.mem after [] source.out):=by
  have hlarge:64 < 2 ^ (v + 1):=by rw [Nat.pow_succ]; omega
  have hbufferBound:=buffer_address_lt hcapacity hhit
  have hdoubleBound:2 * offset < 2 ^ (v + 1):=by omega
  let after:=put (put scratch 2 (65 + 2 * offset)) 5 (values[offset] % 2 ^ (v + 1))
  refine ⟨after,put_low (put_low hscratch 2 _ (by omega) (by omega))
    5 _ (by omega) (by omega),by simp [after], ?_⟩
  have h5:(compile extra program)[location source.pc + 5]? =
      some (.jzero 19 (location source.pc + 10)):=by
    simpa [inputLoadBody,TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,TapeRamVirtualCompiler.twoRegister,temporaryRegister,lengthRegister,baseRegister] using
      (inputLoad_fetch hfetch (offset:=5) (by omega))
  have h6:(compile extra program)[location source.pc + 6]?=some (.mul 5 11 3):=by
    simpa [inputLoadBody,TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,TapeRamVirtualCompiler.twoRegister,temporaryRegister,lengthRegister,baseRegister] using
      (inputLoad_fetch hfetch (offset:=6) (by omega))
  have h7:(compile extra program)[location source.pc + 7]?=some (.add 5 5 21):=by
    simpa [inputLoadBody,TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,TapeRamVirtualCompiler.twoRegister,temporaryRegister,lengthRegister,baseRegister] using
      (inputLoad_fetch hfetch (offset:=7) (by omega))
  have h8:(compile extra program)[location source.pc + 8]?=some (.load 11 5):=by
    simpa [inputLoadBody,TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,TapeRamVirtualCompiler.twoRegister,temporaryRegister,lengthRegister,baseRegister] using
      (inputLoad_fetch hfetch (offset:=8) (by omega))
  have h9:(compile extra program)[location source.pc + 9]? =
      some (.jump (location source.pc + 11)):=by
    simpa [inputLoadBody,TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,TapeRamVirtualCompiler.twoRegister,temporaryRegister,lengthRegister,baseRegister] using
      (inputLoad_fetch hfetch (offset:=9) (by omega))
  have hmod3:3 % 2 ^ (v + 1)=3:=Nat.mod_eq_of_lt (by omega)
  have hmod5:5 % 2 ^ (v + 1)=5:=Nat.mod_eq_of_lt (by omega)
  have hmod11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
  have hmod19:19 % 2 ^ (v + 1)=19:=Nat.mod_eq_of_lt (by omega)
  have hmod21:21 % 2 ^ (v + 1)=21:=Nat.mod_eq_of_lt (by omega)
  have hset5 (sc:Nat→ Nat) (value:Nat):
      setCell (v + 1) (merge source.mem sc) 5 value =
        merge source.mem (put sc 2 (value % 2 ^ (v + 1))):=
    set_odd v source.mem sc 5 value (by decide) (by omega)
  have hset11 (sc:Nat→ Nat) (value:Nat):
      setCell (v + 1) (merge source.mem sc) 11 value =
        merge source.mem (put sc 5 (value % 2 ^ (v + 1))):=
    set_odd v source.mem sc 11 value (by decide) (by omega)
  have hread3 (sc:Nat→ Nat):merge source.mem sc 3=sc 1:=by simp [merge]
  have hread5 (sc:Nat→ Nat):merge source.mem sc 5=sc 2:=by simp [merge]
  have hread11 (sc:Nat→ Nat):merge source.mem sc 11=sc 5:=by simp [merge]
  have hread19 (sc:Nat→ Nat):merge source.mem sc 19=sc 9:=by simp [merge]
  have hread21 (sc:Nat→ Nat):merge source.mem sc 21=sc 10:=by simp [merge]
  have hreadBuffer (sc:Nat→ Nat):merge source.mem sc (65 + 2 * offset) =
      sc (32 + offset):=by
    convert merge_odd source.mem sc (32 + offset) using 1 <;> congr 1 <;> omega
  have hbuffer:scratch (32 + offset)=values[offset]:=hscratch.buffer offset hhit
  have hpositive:values.length - offset ≠ 0:=by omega
  have haddr:2 * offset + 65=65 + 2 * offset:=by omega
  have hhigh2:32 + offset ≠ 2:=by omega
  have hhigh5:32 + offset ≠ 5:=by omega
  simp [run,step,state,h5,h6,h7,h8,h9,Instr.effect,
    hmod3,hmod5,hmod11,hmod19,hmod21,hread3,hread5,hread11,
    hread19,hread21,hset5,hset11,hgap,hpositive,hindex,
    hscratch.compiler.2,hscratch.base_eq,Nat.mul_comm offset 2,
    Nat.mod_eq_of_lt hdoubleBound,Nat.mod_eq_of_lt hbufferBound,
    hreadBuffer,put,hbuffer,after,Nat.add_assoc,haddr,hhigh2,hhigh5]

theorem inputLoad_miss {v extra cursor address index offset:Nat} {values:List Nat}
    {program:Program} {source:State} {scratch:Nat→ Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfetch:program[source.pc]?=some (.inputLoad address index))
    (hscratch:AdapterScratch v values cursor scratch)
    (hgap:scratch 9=values.length - offset) (hmiss:values.length≤ offset):
    ∃ after,AdapterScratch v values cursor after∧ after 5=0∧
      run (v + 1) (compile extra program) 2
        (state values (location source.pc + 5) source.mem scratch [] source.out) =
        some (state values (location source.pc + 11) source.mem after [] source.out):=by
  have hlarge:64 < 2 ^ (v + 1):=by rw [Nat.pow_succ]; omega
  refine ⟨put scratch 5 0,put_low hscratch 5 0 (by omega) (by omega),by simp, ?_⟩
  have h5:(compile extra program)[location source.pc + 5]? =
      some (.jzero 19 (location source.pc + 10)):=by
    simpa [inputLoadBody,TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,TapeRamVirtualCompiler.twoRegister,temporaryRegister,lengthRegister,baseRegister] using
      (inputLoad_fetch hfetch (offset:=5) (by omega))
  have h10:(compile extra program)[location source.pc + 10]?=some (.set 11 0):=by
    simpa [inputLoadBody,TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.resultRegister,TapeRamVirtualCompiler.addressRegister,TapeRamVirtualCompiler.twoRegister,temporaryRegister,lengthRegister,baseRegister] using
      (inputLoad_fetch hfetch (offset:=10) (by omega))
  have hmod19:19 % 2 ^ (v + 1)=19:=Nat.mod_eq_of_lt (by omega)
  have hread19:merge source.mem scratch 19=scratch 9:=by simp [merge]
  have hset:=set_odd v source.mem scratch 11 0 (by decide) (by omega)
  simp [run,step,state,h5,h10,Instr.effect,hmod19,hread19,hgap,
    Nat.sub_eq_zero_of_le hmiss,hset,Nat.add_assoc]

theorem inputLoad_run {v extra cursor address index:Nat} {values:List Nat}
    {program:Program} {source:State} {scratch:Nat→ Nat}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfetch:program[source.pc]?=some (.inputLoad address index))
    (hnormal:Normalized v source.mem) (hscratch:AdapterScratch v values cursor scratch):
    ∃ steps≤ 16, ∃ nextScratch,
      AdapterScratch v values cursor nextScratch∧
      run (v + 1) (compile extra program) steps
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16)
          (setCell v source.mem address ((values[source.mem (index % 2 ^ v)]?).getD 0))
          nextScratch [] source.out):=by
  let offset:=source.mem (index % 2 ^ v)
  let after:=put (put (put scratch 2 (2 * (index % 2 ^ v))) 5 offset)
    9 (values.length - offset)
  obtain ⟨hafter,hhead⟩:=inputLoad_head (extra:=extra) hcapacity hfetch hnormal hscratch
  change AdapterScratch v values cursor after at hafter
  change run (v + 1) (compile extra program) 5
    (state values (location source.pc) source.mem scratch [] source.out) =
    some (state values (location source.pc + 5) source.mem after [] source.out) at hhead
  have hindex:after 5=offset:=by simp [after]
  have hgap:after 9=values.length - offset:=by simp [after]
  by_cases hhit:offset < values.length
  · obtain ⟨loaded,hloaded,hvalue,hmiddle⟩:=
      inputLoad_hit (extra:=extra) hcapacity hfetch hafter hindex hgap hhit
    obtain ⟨nextScratch,hnext,hwrite⟩:=
      inputLoad_write (extra:=extra) hcapacity hfetch hloaded
    refine ⟨15,by omega,nextScratch,hnext, ?_⟩
    have hmem:setCell v source.mem address (loaded 5) =
        setCell v source.mem address ((values[offset]?).getD 0):=by
      rw [hvalue]
      funext a
      simp [setCell,hhit,mod_physical_virtual]
    rw [show 15=5 + (5 + 5) by omega,run_add,hhead,Option.bind_some,
      run_add,hmiddle,Option.bind_some,hwrite]
    simp only [hmem,offset]
  · obtain ⟨loaded,hloaded,hvalue,hmiddle⟩:=
      inputLoad_miss (extra:=extra) hcapacity hfetch hafter hgap (by omega)
    obtain ⟨nextScratch,hnext,hwrite⟩:=
      inputLoad_write (extra:=extra) hcapacity hfetch hloaded
    refine ⟨12,by omega,nextScratch,hnext, ?_⟩
    have hmem:setCell v source.mem address (loaded 5) =
        setCell v source.mem address ((values[offset]?).getD 0):=by
      simp [hvalue,List.getElem?_eq_none (by omega:values.length≤ offset)]
    rw [show 12=5 + (2 + 5) by omega,run_add,hhead,Option.bind_some,
      run_add,hmiddle,Option.bind_some,hwrite]
    simp only [hmem,offset]

end Lax759944Proofs.TapeRamBufferedIndexed

end

section

namespace Lax759944Proofs.TapeRamBufferedPrelude

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler

theorem execute_cons (w:Nat) (instruction:Instr) (rest:Program) (s:State):
    execute w (instruction::rest) s =
      (execute w [instruction] s).bind (execute w rest):=
  execute_append w [instruction] rest s

def CoreScratch (v:Nat) (values:List Nat) (scratch:Nat→ Nat):Prop:=
  CompilerScratch v scratch∧ scratch 6=values.length∧ scratch 7=0∧
    scratch 10=65∧ scratch 11=1∧ scratch 12=0

def initialCode (extra:Nat):Program:=TapeRamVirtualCompiler.initialCost ++
  [.set oneRegister 1, .set baseRegister 65, .set zeroRegister 0,
   .read headerRegister, .set lengthRegister extra,
   .add lengthRegister headerRegister lengthRegister, .set cursorRegister 0,
   .store baseRegister headerRegister, .set temporaryRegister 67,
   .sub remainingRegister lengthRegister oneRegister]

def initialScratch (v header:Nat) (tail:List Nat):Nat→ Nat:=
  put (put (put (put (put (put (put (put (put (put (put
    (fun _ => 0) 1 2) 0 (2 ^ v - 1)) 11 1) 10 65) 12 0) 13 header)
    6 (header::tail).length) 7 0) 32 header) 9 67) 8 tail.length

theorem initialScratch_core (v header:Nat) (tail:List Nat):
    CoreScratch v (header::tail) (initialScratch v header tail):=by
  simp [CoreScratch,CompilerScratch,initialScratch,put]

theorem initialScratch_buffer (v header:Nat) (tail:List Nat):
    TapeRamBufferedState.BufferStored [header] (initialScratch v header tail):=by
  intro index hindex
  have hi:index=0:=by simpa using hindex
  subst index
  simp [initialScratch,put,bufferBase]

theorem storeRegister_execute (v pc addressRegister valueRegister target:Nat)
    (memory scratch:Nat→ Nat) (original input output:List Nat)
    (ha:2 * addressRegister + 1 < 2 ^ (v + 1))
    (hv:2 * valueRegister + 1 < 2 ^ (v + 1))
    (ht:2 * target + 1 < 2 ^ (v + 1))
    (haddress:scratch addressRegister=2 * target + 1):
    execute (v + 1) [.store (2 * addressRegister + 1) (2 * valueRegister + 1)]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target (scratch valueRegister % 2 ^ (v + 1))) input output):=by
  have hs:=set_odd v memory scratch (2 * target + 1) (scratch valueRegister) (by omega) ht
  simp only [execute,Instr.effect,state,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hv,
    merge_odd,haddress,hs,Option.bind_some]
  simpa [Nat.add_div,Nat.mul_div_right]

theorem addRegister_execute (v pc target left right:Nat) {original:List Nat}
    (memory scratch:Nat→ Nat) (input output:List Nat)
    (htarget:2 * target + 1 < 2 ^ (v + 1))
    (hleft:2 * left + 1 < 2 ^ (v + 1))
    (hright:2 * right + 1 < 2 ^ (v + 1)):
    execute (v + 1) [.add (2 * target + 1) (2 * left + 1) (2 * right + 1)]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target ((scratch left + scratch right) % 2 ^ (v + 1)))
        input output):=by
  simpa only [BinaryKind.instruction,BinaryKind.value] using
    (binaryRegister_execute .add v pc target left right memory scratch input output
      htarget hleft hright (original:=original))

theorem subRegister_execute (v pc target left right:Nat) {original:List Nat}
    (memory scratch:Nat→ Nat) (input output:List Nat)
    (htarget:2 * target + 1 < 2 ^ (v + 1))
    (hleft:2 * left + 1 < 2 ^ (v + 1))
    (hright:2 * right + 1 < 2 ^ (v + 1)):
    execute (v + 1) [.sub (2 * target + 1) (2 * left + 1) (2 * right + 1)]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target ((scratch left - scratch right) % 2 ^ (v + 1)))
        input output):=by
  simpa only [BinaryKind.instruction,BinaryKind.value] using
    (binaryRegister_execute .sub v pc target left right memory scratch input output
      htarget hleft hright (original:=original))

theorem initialCode_execute (v extra header:Nat) (tail:List Nat)
    (hcapacity:(header::tail).length + 32 < 2 ^ v)
    (hlength:(header::tail).length=header + extra)
    (hwords:∀ value∈ header::tail,value < 2 ^ v):
    execute (v + 1) (initialCode extra) (initState (header::tail)) =
      some (state (header::tail) 14 (fun _ => 0)
        (initialScratch v header tail) tail []):=by
  have hpow:2 ^ (v + 1)=2 ^ v * 2:=Nat.pow_succ _ _
  have hnonempty:0 < (header::tail).length:=by simp
  have hh:header < 2 ^ v:=hwords header (by simp)
  have hsmall:16≤ 2 ^ (v + 1):=by omega
  have hinitial:initState (header::tail) =
      state (header::tail) 0 (fun _ => 0) (fun _ => 0) (header::tail) []:=by
    simp only [initState,state]
    congr 1
    funext address
    simp [merge]
  rw [hinitial,initialCode,execute_append,
    prelude_execute v 0 (fun _ => 0) (fun _ => 0) (header::tail) [] hsmall]
  simp only [Option.bind_some]
  simp only [oneRegister,baseRegister,zeroRegister,headerRegister,lengthRegister,
    cursorRegister,temporaryRegister,remainingRegister,Nat.zero_add]
  rw [execute_cons,setRegister_execute v 4 11 1 _ _ _ _ (by omega),Option.bind_some]
  rw [execute_cons,setRegister_execute v 5 10 65 _ _ _ _ (by omega),Option.bind_some]
  rw [execute_cons,setRegister_execute v 6 12 0 _ _ _ _ (by omega),Option.bind_some]
  rw [execute_cons,readRegister_execute v 7 13 header tail _ _ _ (by omega),Option.bind_some]
  rw [execute_cons,setRegister_execute v 8 6 extra _ _ _ _ (by omega),Option.bind_some]
  rw [execute_cons,addRegister_execute v 9 6 13 6 _ _ _ _
    (by omega) (by omega) (by omega),Option.bind_some]
  rw [execute_cons,setRegister_execute v 10 7 0 _ _ _ _ (by omega),Option.bind_some]
  rw [execute_cons,storeRegister_execute v 11 10 13 32 _ _ _ _ _
    (by omega) (by omega) (by omega) (by
      simp (disch:=omega) [put,Nat.mod_eq_of_lt]),Option.bind_some]
  rw [execute_cons,setRegister_execute v 12 9 67 _ _ _ _ (by omega),Option.bind_some]
  rw [execute_cons,subRegister_execute v 13 8 6 11 _ _ _ _
    (by omega) (by omega) (by omega),Option.bind_some]
  simp (disch:=omega) only [execute,BinaryKind.value,put_same,put_other,
    Nat.mod_eq_of_lt,Nat.zero_mod,put_overwrite]
  simpa only [initialScratch, ← hlength,List.length_cons,Nat.add_sub_cancel]

theorem initialCode_run (v extra header:Nat) (tail:List Nat) (program:Program)
    (hcapacity:(header::tail).length + 32 < 2 ^ v)
    (hlength:(header::tail).length=header + extra)
    (hwords:∀ value∈ header::tail,value < 2 ^ v):
    run (v + 1) (compile extra program) 14 (initState (header::tail)) =
      some (state (header::tail) 14 (fun _ => 0)
        (initialScratch v header tail) tail []):=by
  have hlinear:∀ instruction∈ initialCode extra,StraightLine instruction:=by
    simp [initialCode,TapeRamVirtualCompiler.initialCost,StraightLine]
  have hfetch:∀ index,index < (initialCode extra).length→
      (compile extra program)[(initState (header::tail)).pc + index]? =
        (initialCode extra)[index]?:=by
    intro index hindex
    have hi:index < 14:=by simpa [initialCode,TapeRamVirtualCompiler.initialCost] using hindex
    interval_cases index <;> rfl
  change run (v + 1) (compile extra program) (initialCode extra).length _=_
  rw [run_eq_execute _ _ _ _ hlinear hfetch]
  exact initialCode_execute v extra header tail hcapacity hlength hwords

theorem CoreScratch.put {v:Nat} {values:List Nat} {scratch:Nat→ Nat}
    (hcore:CoreScratch v values scratch) (index value:Nat)
    (hindex:index=5∨ index=8∨ index=9∨ 32≤ index):
    CoreScratch v values (put scratch index value):=by
  rcases hcore with ⟨⟨hmask,htwo⟩,hlength,hcursor,hbase,hone,hzero⟩
  rcases hindex with rfl | rfl | rfl | hindex <;>
    simp (disch:=omega) [CoreScratch,CompilerScratch,put,
      hmask,htwo,hlength,hcursor,hbase,hone,hzero]

theorem buffer_put_low {consumed:List Nat} {scratch:Nat→ Nat}
    (hbuffer:TapeRamBufferedState.BufferStored consumed scratch)
    (index value:Nat) (hindex:index < 32):
    TapeRamBufferedState.BufferStored consumed (put scratch index value):=
  hbuffer.preserve (scratchPreservedFrom_put 32 scratch index value hindex)

theorem buffer_snoc {consumed:List Nat} {scratch:Nat→ Nat}
    (hbuffer:TapeRamBufferedState.BufferStored consumed scratch) (value:Nat):
    TapeRamBufferedState.BufferStored (consumed ++ [value])
      (put scratch (32 + consumed.length) value):=by
  intro index hindex
  by_cases hprefix:index < consumed.length
  · rw [List.getElem_append_left hprefix]
    simpa [put,bufferBase,show index ≠ consumed.length by omega] using
      hbuffer index hprefix
  · have hi:index=consumed.length:=by simp only [List.length_append,List.length_singleton] at hindex; omega
    subst index
    simp [put,bufferBase]

def loopCode:Program:=
  [.read TapeRamVirtualCompiler.resultRegister,
   .store temporaryRegister TapeRamVirtualCompiler.resultRegister,
   .add temporaryRegister temporaryRegister TapeRamVirtualCompiler.twoRegister,
   .sub remainingRegister remainingRegister oneRegister]

def loopScratch (scratch:Nat→ Nat) (consumed:List Nat) (value:Nat)
    (rest:List Nat):Nat→ Nat:=
  put (put (put (put scratch 5 value) (32 + consumed.length) value)
    9 (65 + 2 * (consumed.length + 1))) 8 rest.length

theorem loopCode_execute (v:Nat) (original consumed:List Nat) (value:Nat)
    (rest:List Nat) (scratch:Nat→ Nat)
    (hcapacity:original.length + 32 < 2 ^ v)
    (hsplit:original=consumed ++ value::rest)
    (hvalue:value < 2 ^ v)
    (hcore:CoreScratch v original scratch)
    (hremaining:scratch 8=(value::rest).length)
    (hpointer:scratch 9=65 + 2 * consumed.length):
    execute (v + 1) loopCode
      (state original 15 (fun _ => 0) scratch (value::rest) []) =
      some (state original 19 (fun _ => 0)
        (loopScratch scratch consumed value rest) rest []):=by
  have hpow:2 ^ (v + 1)=2 ^ v * 2:=Nat.pow_succ _ _
  have hlength:original.length=consumed.length + (rest.length + 1):=by simp [hsplit]
  rcases hcore with ⟨⟨hmask,htwo⟩,hlen,hcursor,hbase,hone,hzero⟩
  simp only [loopCode,TapeRamVirtualCompiler.resultRegister,
    TapeRamVirtualCompiler.twoRegister,temporaryRegister,remainingRegister,oneRegister]
  rw [execute_cons,
    readRegister_execute v 15 5 value rest _ _ _ (by omega),Option.bind_some]
  rw [execute_cons,storeRegister_execute v 16 9 5 (32 + consumed.length) _ _ _ _ _
    (by omega) (by omega) (by omega) (by simp [put,hpointer]; omega),Option.bind_some]
  rw [execute_cons,addRegister_execute v 17 9 9 1 _ _ _ _
    (by omega) (by omega) (by omega),Option.bind_some]
  rw [execute_cons,subRegister_execute v 18 8 8 11 _ _ _ _
    (by omega) (by omega) (by omega),Option.bind_some]
  simp (disch:=omega) only [execute,BinaryKind.value,put_same,put_other,
    Nat.mod_eq_of_lt,hremaining,hpointer,htwo,hone,List.length_cons,
    Nat.add_sub_cancel]
  simp only [loopScratch,Nat.mul_add,Nat.mul_one,Nat.add_assoc]

theorem loop_iteration (v extra:Nat) (program:Program)
    (original consumed:List Nat) (value:Nat) (rest:List Nat) (scratch:Nat→ Nat)
    (hcapacity:original.length + 32 < 2 ^ v)
    (hsplit:original=consumed ++ value::rest)
    (hvalue:value < 2 ^ v)
    (hcore:CoreScratch v original scratch)
    (hremaining:scratch 8=(value::rest).length)
    (hpointer:scratch 9=65 + 2 * consumed.length):
    run (v + 1) (compile extra program) 6
      (state original 14 (fun _ => 0) scratch (value::rest) []) =
      some (state original 14 (fun _ => 0)
        (loopScratch scratch consumed value rest) rest []):=by
  have hpow:2 ^ (v + 1)=2 ^ v * 2:=Nat.pow_succ _ _
  have h17:17 < 2 ^ (v + 1):=by omega
  have h14:(compile extra program)[14]? =
      some (.jzero remainingRegister (location 0)):=rfl
  have h19:(compile extra program)[19]?=some (.jump 14):=rfl
  have hfirst:run (v + 1) (compile extra program) 1
      (state original 14 (fun _ => 0) scratch (value::rest) []) =
      some (state original 15 (fun _ => 0) scratch (value::rest) []):=by
    simp [run,step,state,h14,Instr.effect,remainingRegister,
      Nat.mod_eq_of_lt h17,merge,hremaining]
  have hbody:run (v + 1) (compile extra program) 4
      (state original 15 (fun _ => 0) scratch (value::rest) []) =
      some (state original 19 (fun _ => 0)
        (loopScratch scratch consumed value rest) rest []):=by
    have hlinear:∀ instruction∈ loopCode,StraightLine instruction:=by
      simp [loopCode,StraightLine]
    have hfetch:∀ index,index < loopCode.length→
        (compile extra program)[(state original 15 (fun _ => 0) scratch
          (value::rest) []).pc + index]?=loopCode[index]?:=by
      intro index hindex
      have hi:index < 4:=by simpa [loopCode] using hindex
      interval_cases index <;> rfl
    change run (v + 1) (compile extra program) loopCode.length _=_
    rw [run_eq_execute _ _ _ _ hlinear hfetch]
    exact loopCode_execute v original consumed value rest scratch
      hcapacity hsplit hvalue hcore hremaining hpointer
  have hlast:run (v + 1) (compile extra program) 1
      (state original 19 (fun _ => 0) (loopScratch scratch consumed value rest) rest []) =
      some (state original 14 (fun _ => 0) (loopScratch scratch consumed value rest) rest []):=by
    simp [run,step,state,h19,Instr.effect]
  rw [show 6=1 + (4 + 1) by rfl,run_add,hfirst,Option.bind_some,
    run_add,hbody,Option.bind_some,hlast]

theorem loop_runs (v extra:Nat) (program:Program) (original:List Nat)
    (consumed rest:List Nat) (scratch:Nat→ Nat)
    (hcapacity:original.length + 32 < 2 ^ v)
    (hsplit:original=consumed ++ rest)
    (hwords:∀ value∈ original,value < 2 ^ v)
    (hcore:CoreScratch v original scratch)
    (hremaining:scratch 8=rest.length)
    (hpointer:scratch 9=65 + 2 * consumed.length)
    (hbuffer:TapeRamBufferedState.BufferStored consumed scratch):
    ∃ finalScratch,
      TapeRamBufferedState.AdapterScratch v original 0 finalScratch∧
      run (v + 1) (compile extra program) (6 * rest.length + 1)
        (state original 14 (fun _ => 0) scratch rest []) =
        some (state original (location 0) (fun _ => 0) finalScratch [] []):=by
  induction rest generalizing consumed scratch with
  | nil =>
      rcases hcore with ⟨hcompiler,hlength,hcursor,hbase,hone,hzero⟩
      refine ⟨scratch, ⟨hcompiler,hlength,hcursor,hbase,hone,hzero,
        Nat.zero_le _, ?_⟩, ?_⟩
      · simpa [hsplit] using hbuffer
      · have hpow:2 ^ (v + 1)=2 ^ v * 2:=Nat.pow_succ _ _
        have h17:17 < 2 ^ (v + 1):=by omega
        have h14:(compile extra program)[14]? =
            some (.jzero remainingRegister (location 0)):=rfl
        simp [run,step,state,h14,Instr.effect,remainingRegister,
          Nat.mod_eq_of_lt h17,merge,hremaining]
  | cons value rest ih =>
      have hvalue:value < 2 ^ v:=hwords value (by simp [hsplit])
      let nextScratch:=loopScratch scratch consumed value rest
      have hcoreNext:CoreScratch v original nextScratch:=
        (((hcore.put 5 value (by omega)).put (32 + consumed.length) value (by omega)).put
          9 (65 + 2 * (consumed.length + 1)) (by omega)).put 8 rest.length (by omega)
      have hremainingNext:nextScratch 8=rest.length:=by simp [nextScratch,loopScratch]
      have hpointerNext:nextScratch 9=65 + 2 * (consumed ++ [value]).length:=by
        simp [nextScratch,loopScratch]
      have hbufferNext:TapeRamBufferedState.BufferStored (consumed ++ [value]) nextScratch:=
        buffer_put_low
          (buffer_put_low (buffer_snoc (buffer_put_low hbuffer 5 value (by omega)) value)
            9 (65 + 2 * (consumed.length + 1)) (by omega)) 8 rest.length (by omega)
      have hsplitNext:original=(consumed ++ [value]) ++ rest:=by
        simpa only [List.append_assoc,List.singleton_append] using hsplit
      obtain ⟨finalScratch,hfinal,hrun⟩:=ih (consumed ++ [value]) nextScratch
        hsplitNext hcoreNext hremainingNext hpointerNext hbufferNext
      refine ⟨finalScratch,hfinal, ?_⟩
      rw [show 6 * (value::rest).length + 1=6 + (6 * rest.length + 1) by
        simp only [List.length_cons]; omega,run_add,
        loop_iteration v extra program original consumed value rest scratch
          hcapacity hsplit hvalue hcore hremaining hpointer,Option.bind_some]
      exact hrun

theorem compile_start (v extra header:Nat) (tail:List Nat) (program:Program)
    (hcapacity:(header::tail).length + 32 < 2 ^ v)
    (hlength:(header::tail).length=header + extra)
    (hwords:∀ value∈ header::tail,value < 2 ^ v):
    ∃ scratch,
      TapeRamBufferedState.AdapterScratch v (header::tail) 0 scratch∧
      run (v + 1) (compile extra program) (6 * (header::tail).length + 9)
        (initState (header::tail)) =
        some (state (header::tail) (location 0) (fun _ => 0) scratch [] []):=by
  obtain ⟨scratch,hscratch,hloop⟩:=loop_runs v extra program (header::tail)
    [header] tail (initialScratch v header tail) hcapacity rfl hwords
    (initialScratch_core v header tail) (by simp [initialScratch])
    (by simp [initialScratch]) (initialScratch_buffer v header tail)
  refine ⟨scratch,hscratch, ?_⟩
  rw [show 6 * (header::tail).length + 9=14 + (6 * tail.length + 1) by
    simp only [List.length_cons]; omega,run_add,
    initialCode_run v extra header tail program hcapacity hlength hwords,Option.bind_some]
  exact hloop

end Lax759944Proofs.TapeRamBufferedPrelude

end

section

namespace Lax759944Proofs.TapeRamBufferedSimulation

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler TapeRamBufferedState

theorem effect_input {v:Nat} {instruction:Instr} {source next:State}
    (heffect:instruction.effect v source=some next):next.input=source.input:=by
  cases instruction <;> simp only [Instr.effect] at heffect
  all_goals try { cases heffect; rfl }
  case halt => cases heffect
  case read address =>
    cases hinput:source.inp with
    | nil => simp [hinput] at heffect
    | cons value rest => simp [hinput] at heffect; cases heffect; rfl

def withoutCursor (source:State):State:= { source with inp:= [] }

theorem core_effect_withoutCursor {v:Nat} {instruction:Instr} {source next:State}
    (hcore:CoreInstruction instruction)
    (heffect:instruction.effect v source=some next):
    instruction.effect v (withoutCursor source)=some (withoutCursor next):=by
  cases instruction <;> simp only [CoreInstruction] at hcore
  all_goals try contradiction
  all_goals simp only [Instr.effect] at heffect ⊢
  all_goals try { cases heffect; rfl }
  all_goals contradiction

theorem core_run_paddedBody {v extra:Nat} {values:List Nat} {program:Program}
    {instruction:Instr} {source next:State} {scratch:Nat→ Nat} {cursor:Nat}
    (hcapacity:16≤ 2 ^ (v + 1)) (hfetch:program[source.pc]?=some instruction)
    (hcore:CoreInstruction instruction) (hinput:source.input=values)
    (hscratch:AdapterScratch v values cursor scratch)
    (hnormal:Normalized v source.mem)
    (heffect:instruction.effect v source=some next):
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch∧ BranchReady v instruction source nextScratch∧
      run (v + 1) (compile extra program) 16
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16) next.mem nextScratch [] next.out):=by
  have hnextInput:=(effect_input heffect).trans hinput
  have heffect':=core_effect_withoutCursor hcore heffect
  rcases TapeRamVirtualSimulation.paddedBody_effect (physicalPc:=location source.pc)
      (source:=withoutCursor source) (next:=withoutCursor next) hcapacity hscratch.compiler hnormal heffect' with
    ⟨nextScratch,hcompiler,hready,hhigh,hbody⟩
  refine ⟨nextScratch,hscratch.preserve hcompiler hhigh, ?_, ?_⟩
  · cases instruction <;> simp only [CoreInstruction] at hcore
    all_goals try contradiction
    all_goals simpa only [BranchReady,TapeRamVirtualSimulation.BranchReady,withoutCursor] using hready
  · have hlinear:∀ i∈ TapeRamVirtualCompiler.paddedBody instruction,StraightLine i:=by
      intro i hi
      simp only [TapeRamVirtualCompiler.paddedBody,List.mem_append,List.mem_replicate] at hi
      rcases hi with hi | ⟨_,rfl⟩
      · exact body_straightLine instruction i hi
      · trivial
    have hprefix:∀ k,k < (TapeRamVirtualCompiler.paddedBody instruction).length→
        (compile extra program)[(state values (location source.pc) source.mem scratch [] source.out).pc + k]? =
          (TapeRamVirtualCompiler.paddedBody instruction)[k]?:=by
      intro k hk
      rw [← paddedBody_eq_of_core program.length source.pc instruction hcore]
      exact compile_get_paddedBody extra program source.pc instruction hfetch k (by simpa using hk)
    rw [show 16=(TapeRamVirtualCompiler.paddedBody instruction).length by simp,
      run_eq_execute _ _ _ _ hlinear hprefix]
    simpa only [withoutCursor,hinput,hnextInput,TapeRamVirtualCompiler.paddedBody_length] using hbody

theorem run_branch {v extra:Nat} {values remaining:List Nat} {program:Program} {i:Instr}
    {source next:State} {scratch:Nat→ Nat}
    (hcapacity:16≤ 2 ^ (v + 1)) (hfetch:program[source.pc]?=some i)
    (hready:BranchReady v i source scratch)
    (heffect:i.effect v source=some next):
    ∃ cost,1≤ cost∧ cost≤ 2∧
      run (v + 1) (compile extra program) cost
        (state values (location source.pc + 16) next.mem scratch remaining next.out) =
        some (state values (location next.pc) next.mem scratch remaining next.out):=by
  have hfirst:=compile_get_branch extra program source.pc i hfetch 0 (by omega)
  have hsecond:=compile_get_branch extra program source.pc i hfetch 1 (by omega)
  have h11:11 % 2 ^ (v + 1)=11:=Nat.mod_eq_of_lt (by omega)
  cases i with
  | set address value =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | load target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | store addressCell valueCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | add target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | sub target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | mul target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | div target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | and target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | shiftl target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | not target sourceCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | jump target =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | jzero address target =>
      simp only [Instr.effect] at heffect
      cases heffect
      simp only [BranchReady] at hready
      have htest:merge source.mem scratch 11=source.mem (address % 2 ^ v):=by
        calc
          merge source.mem scratch 11=scratch 5:=by
            simpa using merge_odd source.mem scratch 5
          _=source.mem (address % 2 ^ v):=hready
      by_cases hzero:source.mem (address % 2 ^ v)=0
      · refine ⟨1,by omega,by omega, ?_⟩
        simp [run,step,hfirst,branch,Instr.effect,state,h11,htest,hzero,
          TapeRamVirtualCompiler.resultRegister]
      · refine ⟨2,by omega,by omega, ?_⟩
        simp [run,step,hfirst,hsecond,branch,Instr.effect,state,h11,
          htest,hzero,TapeRamVirtualCompiler.resultRegister]
  | jeof target =>
      simp only [Instr.effect] at heffect
      cases heffect
      simp only [BranchReady] at hready
      have htest:merge source.mem scratch 11=scratch 5:=by
        exact merge_odd source.mem scratch 5
      by_cases hempty:source.inp=[]
      · have hzero:=hready.mpr hempty
        refine ⟨1,by omega,by omega, ?_⟩
        simp [run,step,hfirst,branch,Instr.effect,state,
          TapeRamVirtualCompiler.resultRegister,h11,htest,hzero,hempty]
      · have hzero:scratch 5 ≠ 0:=fun h => hempty (hready.mp h)
        refine ⟨2,by omega,by omega, ?_⟩
        simp [run,step,hfirst,hsecond,branch,Instr.effect,state,
          TapeRamVirtualCompiler.resultRegister,h11,htest,hzero,hempty]
  | inputLength address =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | inputLoad target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]
  | halt =>
      simp only [Instr.effect] at heffect
      contradiction
  | read address =>
      simp only [Instr.effect] at heffect
      cases hinput:source.inp with
      | nil => simp [hinput] at heffect
      | cons value rest =>
          simp [hinput] at heffect
          cases heffect
          refine ⟨1,by omega,by omega, ?_⟩
          simp [run,step,hfirst,branch,Instr.effect,state]
  | write address =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1,by omega,by omega, ?_⟩
      simp [run,step,hfirst,branch,Instr.effect,state]

theorem core_effect_inp {v:Nat} {instruction:Instr} {source next:State}
    (hcore:CoreInstruction instruction)
    (heffect:instruction.effect v source=some next):next.inp=source.inp:=by
  cases instruction <;> simp only [CoreInstruction] at hcore
  all_goals try contradiction
  all_goals simp only [Instr.effect] at heffect
  all_goals try { cases heffect; rfl }
  all_goals contradiction

theorem finish_step {v extra bodyCost cursor:Nat} {values:List Nat} {program:Program}
    {instruction:Instr} {source next:State} {scratch nextScratch:Nat→ Nat}
    (hcapacity:16≤ 2 ^ (v + 1)) (hfetch:program[source.pc]?=some instruction)
    (heffect:instruction.effect v source=some next)
    (hnormal:Normalized v source.mem) (hinput:next.input=values)
    (hseq:next.inp=values.drop cursor) (hadapter:AdapterScratch v values cursor nextScratch)
    (hready:BranchReady v instruction source nextScratch) (hcost:bodyCost≤ 16)
    (hbody:run (v + 1) (compile extra program) bodyCost
      (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16) next.mem nextScratch [] next.out)):
    ∃ cost nextPhysical,
      cost≤ 18∧
      run (v + 1) (compile extra program) cost
        (state values (location source.pc) source.mem scratch [] source.out)=some nextPhysical∧
      Simulates v values next nextPhysical:=by
  rcases run_branch (extra:=extra) (values:=values) (remaining:= []) hcapacity hfetch hready heffect with
    ⟨branchCost,_,hbranchCost,hbranch⟩
  let nextPhysical:=state values (location next.pc) next.mem nextScratch [] next.out
  refine ⟨bodyCost + branchCost,nextPhysical,by omega, ?_, ?_⟩
  · rw [run_add,hbody,Option.bind_some,hbranch]
  · exact ⟨cursor,nextScratch,hinput,hseq,
      TapeRamVirtualSimulation.normalized_effect hnormal heffect,hadapter,rfl⟩

theorem simulation_step {v extra:Nat} {values:List Nat} {program:Program}
    {source next physical:State}
    (hcapacity:values.length + 32 < 2 ^ v)
    (hfit:∀ value∈ values,value < 2 ^ v)
    (hsimulates:Simulates v values source physical)
    (hstep:step v program source=some next):
    ∃ cost nextPhysical,
      cost≤ 18∧ run (v + 1) (compile extra program) cost physical=some nextPhysical∧
      Simulates v values next nextPhysical:=by
  rcases hsimulates with ⟨cursor,scratch,hinput,hseq,hnormal,hadapter,rfl⟩
  have hlarge:=TapeRamBufferedInputs.large_capacity hcapacity
  simp only [step] at hstep
  cases hfetch:program[source.pc]? with
  | none => simp [hfetch] at hstep
  | some instruction =>
      rw [hfetch] at hstep
      simp only [Option.bind_some] at hstep
      have hnextInput:=(effect_input hstep).trans hinput
      by_cases hcore:CoreInstruction instruction
      · rcases core_run_paddedBody (extra:=extra) (by omega) hfetch hcore hinput hadapter
          hnormal hstep with ⟨nextScratch,hnextAdapter,hready,hbody⟩
        exact finish_step (by omega) hfetch hstep hnormal hnextInput
          ((core_effect_inp hcore hstep).trans hseq) hnextAdapter hready (by omega) hbody
      · cases instruction <;> simp only [CoreInstruction] at hcore
        all_goals try contradiction
        case read address =>
          have hnonempty:source.inp ≠ []:=by
            intro hnil
            simp [Instr.effect,hnil] at hstep
          have hcursor:cursor < values.length:=by
            by_contra h
            exact hnonempty (hseq.trans (List.drop_eq_nil_iff.mpr (by omega)))
          have hsourceSeq:=hseq.trans (List.drop_eq_getElem_cons hcursor)
          have hsaved:=hstep
          simp only [Instr.effect,hsourceSeq,List.head?_cons,Option.map_some,List.tail_cons] at hstep
          cases hstep
          rcases TapeRamBufferedRead.read_run (extra:=extra) (memory:=source.mem)
              (output:=source.out) hcapacity hfit hfetch hadapter hcursor with
            ⟨nextScratch,hnextAdapter,hbody⟩
          exact finish_step (by omega) hfetch hsaved hnormal hnextInput rfl
            hnextAdapter (by trivial) (by omega) hbody
        case inputLength address =>
          have hsaved:=hstep
          simp only [Instr.effect] at hstep
          cases hstep
          rcases TapeRamBufferedInputs.inputLength_run (extra:=extra)
              hcapacity hfetch hadapter with ⟨nextScratch,hnextAdapter,hbody⟩
          apply finish_step (bodyCost:=16) (by omega) hfetch hsaved hnormal hnextInput hseq
            hnextAdapter (by trivial) (by omega)
          simpa only [hinput] using hbody
        case inputLoad address index =>
          have hsaved:=hstep
          simp only [Instr.effect] at hstep
          cases hstep
          rcases TapeRamBufferedIndexed.inputLoad_run (extra:=extra)
              hcapacity hfetch hnormal hadapter with
            ⟨bodyCost,hbodyCost,nextScratch,hnextAdapter,hbody⟩
          apply finish_step (by omega) hfetch hsaved hnormal hnextInput hseq
            hnextAdapter (by trivial) hbodyCost
          simpa only [hinput,Nat.mod_eq_of_lt (hnormal _)] using hbody
        case jeof target =>
          have hsaved:=hstep
          simp only [Instr.effect] at hstep
          cases hstep
          rcases TapeRamBufferedInputs.jeof_run (extra:=extra)
              hcapacity hfetch hseq hadapter with ⟨nextScratch,hnextAdapter,hready,hbody⟩
          exact finish_step (by omega) hfetch hsaved hnormal hnextInput hseq
            hnextAdapter hready (by omega) hbody

theorem simulation_run {v extra time:Nat} {values:List Nat} {program:Program}
    {source next physical:State} (hcapacity:values.length + 32 < 2 ^ v)
    (hfit:∀ value∈ values,value < 2 ^ v)
    (hsimulates:Simulates v values source physical)
    (hrun:run v program time source=some next):
    ∃ cost nextPhysical,
      cost≤ 18 * time∧ run (v + 1) (compile extra program) cost physical=some nextPhysical∧
      Simulates v values next nextPhysical:=by
  induction time generalizing source next physical with
  | zero =>
      simp only [run] at hrun
      cases hrun
      exact ⟨0,physical,by omega,by simp [run],hsimulates⟩
  | succ time ih =>
      simp only [run] at hrun
      cases hfirst:step v program source with
      | none => simp [hfirst] at hrun
      | some middle =>
          rw [hfirst] at hrun
          simp only [Option.bind_some] at hrun
          rcases simulation_step (extra:=extra) hcapacity hfit hsimulates hfirst with
            ⟨firstCost,middlePhysical,hfirstCost,hfirstRun,hmiddle⟩
          rcases ih hmiddle hrun with ⟨restCost,nextPhysical,hrestCost,hrestRun,hnext⟩
          refine ⟨firstCost + restCost,nextPhysical,by omega, ?_,hnext⟩
          rw [run_add,hfirstRun,Option.bind_some,hrestRun]

theorem simulation_halt {v extra:Nat} {values:List Nat} {program:Program}
    {source physical:State} (hcapacity:values.length + 32 < 2 ^ v)
    (hsimulates:Simulates v values source physical)
    (hhalt:step v program source=none):
    ∃ cost final,
      cost≤ 16∧ run (v + 1) (compile extra program) cost physical=some final∧
      step (v + 1) (compile extra program) final=none∧ final.out=source.out:=by
  rcases hsimulates with ⟨cursor,scratch,hinput,hseq,hnormal,hadapter,rfl⟩
  have hlarge:=TapeRamBufferedInputs.large_capacity hcapacity
  simp only [step] at hhalt
  cases hfetch:program[source.pc]? with
  | none =>
      have hpc:program.length≤ source.pc:=List.getElem?_eq_none_iff.mp hfetch
      refine ⟨0,state values (location source.pc) source.mem scratch [] source.out,
        by omega,by simp [run], ?_,rfl⟩
      by_cases hequal:source.pc=program.length
      · simp only [step,state,hequal,compile_get_halt,Option.bind_some,Instr.effect]
      · have houtside:=compile_get_outside extra program source.pc (by omega)
        simp only [step,state,houtside,Option.bind_none]
  | some instruction =>
      rw [hfetch] at hhalt
      simp only [Option.bind_some] at hhalt
      cases instruction with
      | halt =>
          let padding:Program:=List.replicate 16 (.set 5 0)
          have hpaddingDef:paddedBody program.length source.pc Instr.halt=padding:=rfl
          have hlinear:∀ i∈ padding,StraightLine i:=by
            simp [padding,StraightLine]
          have hprefix:∀ k,k < padding.length→
              (compile extra program)[location source.pc + k]?=padding[k]?:=by
            intro k hk
            rw [← hpaddingDef]
            exact compile_get_paddedBody extra program source.pc Instr.halt hfetch k
              (by simpa [padding] using hk)
          rcases padding_execute (original:=values) v 16 (location source.pc) source.mem scratch
              [] source.out (by omega) hadapter.compiler with
            ⟨nextScratch,_,_,_,hpadding⟩
          let final:=state values (location source.pc + 16) source.mem nextScratch [] source.out
          have hrun:run (v + 1) (compile extra program) 16
              (state values (location source.pc) source.mem scratch [] source.out)=some final:=by
            rw [show 16=padding.length by simp [padding],
              run_eq_execute _ _ _ _ hlinear hprefix]
            exact hpadding
          have hbranch:=compile_get_branch extra program source.pc Instr.halt hfetch 0 (by omega)
          simp only [Nat.add_zero,branch,List.getElem?_cons_zero] at hbranch
          refine ⟨16,final,by omega,hrun, ?_,rfl⟩
          simp only [step,final,state,hbranch,Option.bind_some,Instr.effect]
      | read address =>
          cases hremaining:source.inp with
          | nil =>
              have hcursor:cursor=values.length:=by
                have hle:=List.drop_eq_nil_iff.mp (hseq.symm.trans hremaining)
                have:=hadapter.cursor_le
                omega
              subst cursor
              rcases TapeRamBufferedRead.read_exhausted (extra:=extra) (memory:=source.mem)
                  (output:=source.out) hcapacity hfetch hadapter with
                ⟨final,hrun,hterminal,houtput⟩
              exact ⟨2,final,by omega,hrun,hterminal,houtput⟩
          | cons value rest => simp [Instr.effect,hremaining] at hhalt
      | set address value => simp [Instr.effect] at hhalt
      | load target addressCell => simp [Instr.effect] at hhalt
      | store addressCell valueCell => simp [Instr.effect] at hhalt
      | add target left right => simp [Instr.effect] at hhalt
      | sub target left right => simp [Instr.effect] at hhalt
      | mul target left right => simp [Instr.effect] at hhalt
      | div target left right => simp [Instr.effect] at hhalt
      | and target left right => simp [Instr.effect] at hhalt
      | shiftl target left right => simp [Instr.effect] at hhalt
      | not target sourceCell => simp [Instr.effect] at hhalt
      | jump target => simp [Instr.effect] at hhalt
      | jzero address target => simp [Instr.effect] at hhalt
      | write address => simp [Instr.effect] at hhalt
      | jeof target => simp [Instr.effect] at hhalt
      | inputLength address => simp [Instr.effect] at hhalt
      | inputLoad target addressCell => simp [Instr.effect] at hhalt

theorem runsTo_compile {v extra header time:Nat} {program:Program}
    {tail output:List Nat}
    (hlength:(header::tail).length=header + extra)
    (hfit:∀ value∈ header::tail,value < 2 ^ v)
    (hcapacity:(header::tail).length + 32 < 2 ^ v)
    (hrun:RunsTo v program (header::tail) output time):
    ∃ physicalTime≤ 18 * time + 6 * (header::tail).length + 26,
      RunsTo (v + 1) (compile extra program) (header::tail) output physicalTime:=by
  rcases hrun with ⟨sourceSteps,sourceFinal,hsourceRun,hsourceHalt,houtput,htime⟩
  rcases TapeRamBufferedPrelude.compile_start v extra header tail program hcapacity hlength hfit with
    ⟨scratch,hadapter,hstart⟩
  let start:=state (header::tail) (location 0) (fun _ => 0) scratch [] []
  have hsimulates:Simulates v (header::tail) (initState (header::tail)) start:=by
    refine ⟨0,scratch,rfl,by simp [initState], ?_,hadapter,rfl⟩
    exact TapeRamVirtualSimulation.normalized_init v (header::tail)
  rcases simulation_run (extra:=extra) hcapacity hfit hsimulates hsourceRun with
    ⟨runCost,runFinal,hrunCost,hsimulatedRun,hfinalSimulates⟩
  rcases simulation_halt (extra:=extra) hcapacity hfinalSimulates hsourceHalt with
    ⟨haltCost,final,hhaltCost,hhaltRun,hterminal,hfinalOutput⟩
  have hterminalCost:terminalCost (compile extra program) final≤ 1:=by
    unfold terminalCost
    split <;> omega
  let steps:=6 * (header::tail).length + 9 + runCost + haltCost
  refine ⟨steps + terminalCost (compile extra program) final,by dsimp [steps]; omega,
    steps,final, ?_,hterminal,hfinalOutput.trans houtput,rfl⟩
  change run (v + 1) (compile extra program)
    (6 * (header::tail).length + 9 + runCost + haltCost)
    (initState (header::tail))=some final
  rw [show 6 * (header::tail).length + 9 + runCost + haltCost =
      (6 * (header::tail).length + 9) + (runCost + haltCost) by omega,
    run_add,hstart,Option.bind_some,run_add,hsimulatedRun,Option.bind_some,hhaltRun]

end Lax759944Proofs.TapeRamBufferedSimulation

end

section

namespace Lax759944Proofs.LegacyRamBridge

def embedInstr:Lax759944Proofs.Legacy.Ram.Instr→ Lax808846.Ram.Instr
  | .set a n => .set a n
  | .load a b => .load a b
  | .store a b => .store a b
  | .add a b c => .add a b c
  | .sub a b c => .sub a b c
  | .mul a b c => .mul a b c
  | .div a b c => .div a b c
  | .and a b c => .and a b c
  | .shiftl a b c => .shiftl a b c
  | .not a b => .not a b
  | .jump l => .jump l
  | .jzero a l => .jzero a l
  | .halt => .halt
  | .read a => .read a
  | .write a => .write a

def embedProgram (p:Lax759944Proofs.Legacy.Ram.Program):Lax808846.Ram.Program:=
  p.map embedInstr

def embedState (input:List ℕ) (s:Lax759944Proofs.Legacy.Ram.State):
    Lax808846.Ram.State where
  pc:=s.pc
  mem:=s.mem
  input:=input
  inp:=s.inp
  out:=s.out

@[simp] theorem embed_initState (input:List ℕ):
    embedState input (Lax759944Proofs.Legacy.Ram.initState input) =
      Lax808846.Ram.initState input:=rfl

theorem effect_embed (w:ℕ) (i:Lax759944Proofs.Legacy.Ram.Instr)
    (input:List ℕ) (s:Lax759944Proofs.Legacy.Ram.State):
    (embedInstr i).effect w (embedState input s) =
      (i.effect w s).map (embedState input):=by
  cases i <;> try rfl
  case read a =>
    cases hinp:s.inp <;>
      simp [embedInstr,embedState,Lax759944Proofs.Legacy.Ram.Instr.effect,
        Lax808846.Ram.Instr.effect,hinp]
    rfl

theorem step_embed (w:ℕ) (p:Lax759944Proofs.Legacy.Ram.Program)
    (input:List ℕ) (s:Lax759944Proofs.Legacy.Ram.State):
    Lax808846.Ram.step w (embedProgram p) (embedState input s) =
      (Lax759944Proofs.Legacy.Ram.step w p s).map (embedState input):=by
  simp only [Lax808846.Ram.step,embedProgram,embedState,
    List.getElem?_map,Lax759944Proofs.Legacy.Ram.step]
  cases hfetch:p[s.pc]? with
  | none => rfl
  | some i => exact effect_embed w i input s

theorem run_embed (w:ℕ) (p:Lax759944Proofs.Legacy.Ram.Program)
    (t:ℕ) (input:List ℕ) (s:Lax759944Proofs.Legacy.Ram.State):
    Lax808846.Ram.run w (embedProgram p) t (embedState input s) =
      (Lax759944Proofs.Legacy.Ram.run w p t s).map (embedState input):=by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      simp only [Lax808846.Ram.run,Lax759944Proofs.Legacy.Ram.run,step_embed]
      cases hstep:Lax759944Proofs.Legacy.Ram.step w p s with
      | none => rfl
      | some s' => exact ih s'

end Lax759944Proofs.LegacyRamBridge

end

section

namespace Lax759944Proofs.LegacyRamProjection

open LegacyRamBridge

def IsLegacy:Lax808846.Ram.Instr→ Prop
  | .jeof _ | .inputLength _ | .inputLoad _ _ => False
  | _ => True

def eraseInstr:Lax808846.Ram.Instr→ Legacy.Ram.Instr
  | .set a n => .set a n
  | .load a b => .load a b
  | .store a b => .store a b
  | .add a b c => .add a b c
  | .sub a b c => .sub a b c
  | .mul a b c => .mul a b c
  | .div a b c => .div a b c
  | .and a b c => .and a b c
  | .shiftl a b c => .shiftl a b c
  | .not a b => .not a b
  | .jump l => .jump l
  | .jzero a l => .jzero a l
  | .halt => .halt
  | .read a => .read a
  | .write a => .write a
  | .jeof _ | .inputLength _ | .inputLoad _ _ => .halt

def eraseProgram (p:Lax808846.Ram.Program):Legacy.Ram.Program:=
  p.map eraseInstr

theorem embed_erase_instr {i:Lax808846.Ram.Instr} (hi:IsLegacy i):
    embedInstr (eraseInstr i)=i:=by
  cases i <;> simp_all +zetaDelta [IsLegacy,eraseInstr,embedInstr]

theorem embed_erase_program {p:Lax808846.Ram.Program}
    (hp:∀ i∈ p,IsLegacy i):embedProgram (eraseProgram p)=p:=by
  simp only [embedProgram,eraseProgram,List.map_map]
  calc
    p.map (embedInstr ∘ eraseInstr)=p.map id:=
      List.map_congr_left (fun i hi => embed_erase_instr (hp i hi))
    _=p:=List.map_id p

theorem runsTo_embed {w t:ℕ} {p:Legacy.Ram.Program}
    {input output:List ℕ}
    (h:Lax808846.Ram.RunsTo w (embedProgram p) input output t):
    ∃ k≤ t,Legacy.Ram.RunsTo w p input output k:=by
  obtain ⟨k,s,hr,hh,ho,ht⟩:=h
  have hr':=run_embed w p k input (Legacy.Ram.initState input)
  rw [embed_initState] at hr'
  cases he:Legacy.Ram.run w p k (Legacy.Ram.initState input) with
  | none => simp [he,hr] at hr'
  | some q =>
      have hs:embedState input q=s:=by
        simpa [he,hr] using hr'.symm
      subst s
      refine ⟨k,by omega,q,he, ?_,ho⟩
      have hh':=step_embed w p input q
      rw [hh] at hh'
      cases hs:Legacy.Ram.step w p q with
      | none => rfl
      | some q' => simp [hs] at hh'

theorem runsTo_erase {w t:ℕ} {p:Lax808846.Ram.Program}
    {input output:List ℕ} (hp:∀ i∈ p,IsLegacy i)
    (h:Lax808846.Ram.RunsTo w p input output t):
    ∃ k≤ t,Legacy.Ram.RunsTo w (eraseProgram p) input output k:=by
  apply runsTo_embed
  simpa [embed_erase_program hp] using h

end Lax759944Proofs.LegacyRamProjection

end

section

namespace Lax759944Proofs.TapeRamBufferedLegacy

open Lax808846.Ram LegacyRamProjection TapeRamBufferedCompiler

theorem prelude_isLegacy (extra:Nat):
    ∀ i∈ initialCost extra,IsLegacy i:=by
  simp [initialCost,TapeRamVirtualCompiler.initialCost,IsLegacy]

theorem body_isLegacy (programLength pc:Nat) (instruction:Instr):
    ∀ i∈ body programLength pc instruction,IsLegacy i:=by
  cases instruction <;>
    simp [body,readBody,inputLoadBody,TapeRamVirtualCompiler.body,
      TapeRamVirtualCompiler.readCell,TapeRamVirtualCompiler.writeCell,IsLegacy]

theorem paddedBody_isLegacy (programLength pc:Nat) (instruction:Instr):
    ∀ i∈ paddedBody programLength pc instruction,IsLegacy i:=by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact body_isLegacy programLength pc instruction i hi
  · have heq:=(List.mem_replicate.mp hi).2
    subst i
    trivial

theorem branch_isLegacy (pc:Nat) (instruction:Instr):
    ∀ i∈ branch pc instruction,IsLegacy i:=by
  cases instruction <;> simp [branch,IsLegacy]

theorem blocks_isLegacy (programLength pc:Nat) (program:Program):
    ∀ i∈ blocks programLength pc program,IsLegacy i:=by
  induction program generalizing pc with
  | nil => simp [blocks]
  | cons instruction rest ih =>
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · rcases List.mem_append.mp hi with hi | hi
        · exact paddedBody_isLegacy programLength pc instruction i hi
        · exact branch_isLegacy pc instruction i hi
      · exact ih (pc + 1) i hi

theorem compile_isLegacy (extra:Nat) (program:Program):
    ∀ i∈ compile extra program,IsLegacy i:=by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact prelude_isLegacy extra i hi
    · exact blocks_isLegacy program.length 0 program i hi
  · have heq:i=.halt:=by simpa using hi
    subst i
    trivial

def lower (extra:Nat) (program:Program):Legacy.Ram.Program:=
  eraseProgram (compile extra program)

theorem runsTo_lower {extra w t:Nat} {program:Program} {input output:List Nat}
    (h:RunsTo w (compile extra program) input output t):
    ∃ k≤ t,Legacy.Ram.RunsTo w (lower extra program) input output k:=
  runsTo_erase (compile_isLegacy extra program) h

end Lax759944Proofs.TapeRamBufferedLegacy

end

section

namespace Lax759944Proofs.TapeRamNativeLowering

def lower (program:Lax808846.Ram.Program):Legacy.Ram.Program:=
  TapeRamBufferedLegacy.lower 1 program

theorem runsTo (program:Lax808846.Ram.Program) (v:Nat)
    (input output:List Nat) (time:Nat)
    (hfit:∀ value∈ input.length::input,value < 2 ^ v)
    (hcapacity:input.length + 33 < 2 ^ v)
    (hrun:Lax808846.Ram.RunsTo v program (input.length::input) output time):
    ∃ legacyTime≤ 18 * time + 6 * (input.length + 1) + 26,
      Legacy.Ram.RunsTo (v + 1) (lower program)
        (input.length::input) output legacyTime:=by
  obtain ⟨physicalTime,htime,hphysical⟩:=
    TapeRamBufferedSimulation.runsTo_compile (extra:=1)
      (header:=input.length) (tail:=input) (by simp) hfit (by simpa [Nat.add_assoc] using hcapacity) hrun
  obtain ⟨legacyTime,hlegacyTime,hlegacy⟩:=TapeRamBufferedLegacy.runsTo_lower hphysical
  exact ⟨legacyTime,hlegacyTime.trans htime,hlegacy⟩

end Lax759944Proofs.TapeRamNativeLowering

end

section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kDecidableEq
open Turing.TM2
variable {κ Λ σ:Type} [DecidableEq κ] {Γ:κ→ Type}

 def cfg (l:Option Λ) (v:σ) (S:∀i,List (Γ i)):Cfg Γ Λ σ:= ⟨l,v,S⟩
 def run (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ):ℕ→ Option (Cfg Γ Λ σ)
   | 0 => some c
   | t+1 => (run code c t).bind (step code)

 theorem run_iter (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ) (t:ℕ):
    run code c t=(fun o:Option (Cfg Γ Λ σ) => o.bind (step code))^[t] (some c):=by
  induction t with
  | zero => rfl
  | succ t ih => rw [run,ih,Function.iterate_succ_apply']

 theorem run_add (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ) (s t:ℕ):
    run code c (s+t)=(run code c s).bind (fun d => run code d t):=by
  induction t with
  | zero => simp only [Nat.add_zero,run]; cases run code c s <;> rfl
  | succ t ih => rw [Nat.add_succ,run,ih]; simp only [Option.bind_assoc,run]

 theorem run_trans (code:Λ→ Stmt Γ Λ σ) (c d e:Cfg Γ Λ σ) (s t:ℕ)
    (hs:run code c s=some d) (ht:run code d t=some e):run code c (s+t)=some e:=by
  rw [run_add,hs,Option.bind_some,ht]

 theorem run_one (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ):run code c 1=step code c:=rfl

 theorem run_first (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ) (t:ℕ):
    run code c (t+1)=(step code c).bind (fun d => run code d t):=by
  rw [show t+1=1+t by omega,run_add,run_one]

 theorem outputs {tm:Turing.FinTM2} (input:List (tm.Γ tm.k₀)) (output:List (tm.Γ tm.k₁))
    (t:ℕ) (h:run tm.m (Turing.initList tm input) t=some (Turing.haltList tm output)):
    Nonempty (Turing.TM2OutputsInTime tm input (some output) t):=by
  refine ⟨⟨⟨t,?_⟩,le_rfl⟩⟩
  have h':=run_iter tm.m (Turing.initList tm input) t
  rw [h'] at h
  exact h

end EdgeSublinearMWIS.Main.RawStack

end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ μ Λ Ω σ τ:Type} [DecidableEq κ] [DecidableEq μ]
variable {Γ:κ→ Type} {Δ:μ→ Type}

 abbrev StackSum (A:κ→ Type) (B:μ→ Type):κ⊕μ→ Type
   | .inl k => A k
   | .inr k => B k

 def extendStore (S:∀k,List (Γ k)) (T:∀k,List (Δ k)):∀k:κ⊕μ,List (StackSum Γ Δ k):=fun k => match k with | .inl k => S k | .inr k => T k
 @[simp] theorem extendStore_inl (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:κ):extendStore S T (.inl k)=S k:=rfl
 @[simp] theorem extendStore_inr (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:μ):extendStore S T (.inr k)=T k:=rfl

 def extendCfg (ret:Ω) (v:τ) (T:∀k,List (Δ k)) (c:Cfg Γ Λ σ):
     Cfg (StackSum Γ Δ) (Λ⊕Ω) (σ×τ):=
   ⟨some (match c.l with | none => .inr ret | some l => .inl l),(c.var,v),extendStore c.stk T⟩
 def extendStmt (ret:Ω):Stmt Γ Λ σ→ Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ)
   | .push k f q => .push (.inl k) (fun v => f v.1) (extendStmt ret q)
   | .pop k f q => .pop (.inl k) (fun v a => (f v.1 a,v.2)) (extendStmt ret q)
   | .peek k f q => .peek (.inl k) (fun v a => (f v.1 a,v.2)) (extendStmt ret q)
   | .load f q => .load (fun v => (f v.1,v.2)) (extendStmt ret q)
   | .branch f q r => .branch (fun v => f v.1) (extendStmt ret q) (extendStmt ret r)
   | .goto f => .goto (fun v => .inl (f v.1))
   | .halt => .goto (fun _ => .inr ret)

 theorem update_extend (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:κ) (x:List (Γ k)):
     Function.update (extendStore S T) (.inl k) x=extendStore (Function.update S k x) T:=by
   funext j
   cases j with
   | inl j =>
     by_cases h:j=k
     · subst j; simp [Function.update,extendStore]
     · simp [Function.update,extendStore,h]
   | inr j => simp [Function.update,extendStore]

 theorem stepAux_extend (ret:Ω) (q:Stmt Γ Λ σ) (v:σ) (w:τ)
     (S:∀k,List (Γ k)) (T:∀k,List (Δ k)):
     stepAux (extendStmt ret q) (v,w) (extendStore S T)=extendCfg ret w T (stepAux q v S):=by
   induction q generalizing v S with
   | push k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     rw [update_extend]
     exact ih _ _
   | pop k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     rw [update_extend]
     exact ih _ _
   | peek k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     exact ih _ _
   | load f q ih => simpa only [extendStmt,stepAux,extendStore_inl] using ih (f v) S
   | branch f q r iq ir =>
     cases hf:f v <;> simp only [extendStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl

 theorem step_extend (ret:Ω) (code:Λ→ Stmt Γ Λ σ)
     (target:Λ⊕Ω→ Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ))
     (hcode:∀l,target (.inl l)=extendStmt ret (code l))
     (c:Cfg Γ Λ σ) (w:τ) (T:∀k,List (Δ k)) (l:Λ) (hc:c.l=some l):
     step target (extendCfg ret w T c)=(step code c).map (extendCfg ret w T):=by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [extendCfg,step,hcode,Option.map_some]
   exact congrArg some (stepAux_extend ret (code l) v w S T)

 theorem run_extend (ret:Ω) (code:Λ→ Stmt Γ Λ σ)
     (target:Λ⊕Ω→ Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ))
     (hcode:∀l,target (.inl l)=extendStmt ret (code l))
     (c d:Cfg Γ Λ σ) (w:τ) (T:∀k,List (Δ k)) (t:ℕ)
     (hr:RawStack.run code c t=some d):
     RawStack.run target (extendCfg ret w T c) t=some (extendCfg ret w T d):=by
   induction t generalizing c with
   | zero => simp only [RawStack.run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [RawStack.run_first] at hr ⊢
     cases hc:c.l with
     | none =>
       have hn:step code c=none:=by cases c; simp_all +zetaDelta [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs:∃ e,step code c=some e:=by cases c; simp_all +zetaDelta [step]
       obtain ⟨e,he⟩:=hs
       rw [step_extend ret code target hcode c w T l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.TernaryAdapter
open Turing.TM2 ProgramComposition Lax759944.BinaryWordEncoding
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def decodePair (a b:Bool):Symbol:=if a then .one else if b then .zero else .separator

 @[simp] theorem decode_symbol (s:Symbol):decodePair (firstBit s) (secondBit s)=s:=by
   cases s <;> rfl
 @[simp] theorem binarySymbols_length (xs:List Symbol):(binarySymbols xs).length=2*xs.length:=by
   induction xs with
   | nil => rfl
   | cons a xs ih => simp only [binarySymbols,List.flatMap_cons,List.length_append,symbolBits,List.length_cons,List.length_nil] at *; omega

 inductive Extra where | raw | output | symbols deriving Fintype,DecidableEq
 def ExtraAlphabet:Extra→ Type
   | .raw | .output => Bool
   | .symbols => Symbol
 instance (k:Extra):Fintype (ExtraAlphabet k):=by cases k <;> dsimp [ExtraAlphabet] <;> infer_instance
 inductive Phase where | first | second | input | output | finish deriving Fintype,DecidableEq
 abbrev Aux:=Option Bool × Option Symbol
 abbrev Machine:=Turing.TM2ComputableAux Symbol Symbol
 abbrev K (H:Machine):=H.tm.K ⊕ Extra
 abbrev Alphabet (H:Machine):=StackSum H.tm.Γ ExtraAlphabet
 abbrev Label (H:Machine):=H.tm.Λ ⊕ Phase
 abbrev State (H:Machine):=H.tm.σ × Aux
 def next {H:Machine} (p:Phase):Stmt (Alphabet H) (Label H) (State H):=.goto (fun _ => .inr p)
 def clearedNext {H:Machine} (p:Phase):Stmt (Alphabet H) (Label H) (State H):=
   .load (fun v => (v.1,(none,none))) (next p)
 def code (H:Machine):Label H→ Stmt (Alphabet H) (Label H) (State H)
   | .inl l => extendStmt .output (H.tm.m l)
   | .inr .first =>
     .pop (.inr .raw) (fun v a => (v.1,(a,none)))
       (.branch (fun v => v.2.1.isSome) (next .second) (next .input))
   | .inr .second =>
     .pop (.inr .raw) (fun v a => (v.1,(none,some (decodePair (v.2.1.getD false) (a.getD false)))))
       (.push (.inr .symbols) (fun v => v.2.2.getD .separator) (clearedNext .first))
   | .inr .input =>
     .pop (.inr .symbols) (fun v a => (v.1,(none,a)))
       (.branch (fun v => v.2.2.isSome)
         (.push (.inl H.tm.k₀) (fun v => H.inputAlphabet.symm (v.2.2.getD .separator)) (clearedNext .input))
         (.load (fun _ => (H.tm.initialState,(none,none))) (.goto (fun _ => .inl H.tm.main))))
   | .inr .output =>
     .pop (.inl H.tm.k₁) (fun v a => (v.1,(none,a.map H.outputAlphabet)))
       (.branch (fun v => v.2.2.isSome)
         (.push (.inr .raw) (fun v => firstBit (v.2.2.getD .separator))
           (.push (.inr .raw) (fun v => secondBit (v.2.2.getD .separator)) (clearedNext .output)))
         (next .finish))
   | .inr .finish =>
     .pop (.inr .raw) (fun v a => (v.1,(a,none)))
       (.branch (fun v => v.2.1.isSome)
         (.push (.inr .output) (fun v => v.2.1.getD false) (clearedNext .finish))
         (.load (fun _ => (H.tm.initialState,(none,none))) .halt))
 def machine (H:Machine):Turing.FinTM2 where
   K:=K H
   Γ:=Alphabet H
   Λ:=Label H
   σ:=State H
   k₀:=.inr .raw
   k₁:=.inr .output
   initialState:=(H.tm.initialState,(none,none))
   main:=.inr .first
   m:=code H
 def program (H:Machine) (hΓ:∀ k,Finite (H.tm.Γ k)):Program where
   machine:= ⟨machine H,Equiv.refl Bool,Equiv.refl Bool⟩
   finiteAlphabet k:=by
     cases k with
     | inl k => exact hΓ k
     | inr k => change Finite (ExtraAlphabet k); infer_instance
end EdgeSublinearMWIS.Main.TernaryAdapter

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.TernaryAdapter
open Turing.TM2 ProgramComposition RawStack Lax759944.BinaryWordEncoding
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def extras (R O:List Bool) (Y:List Symbol):∀ k:Extra,List (ExtraAlphabet k)
   | .raw => R
   | .output => O
   | .symbols => Y
 theorem right_update {κ μ:Type} [DecidableEq κ] [DecidableEq μ] {Γ:κ→ Type} {Δ:μ→ Type}
     (S:∀ k,List (Γ k)) (E:∀ k,List (Δ k)) (e:μ) (L:List (Δ e)):
     Function.update (extendStore S E) (.inr e) L=extendStore S (Function.update E e L):=by
   funext k
   cases k with
   | inl k => simp [Function.update,extendStore]
   | inr k =>
     by_cases h:k=e
     · subst k; simp [Function.update,extendStore]
     · simp [Function.update,extendStore,h]
 @[simp] theorem extras_raw (R O:List Bool) (Y:List Symbol) (L:List Bool):
     Function.update (extras R O Y) Extra.raw L=extras L O Y:=by
   funext k;cases k <;> simp [Function.update,extras]
 @[simp] theorem extras_output (R O:List Bool) (Y:List Symbol) (L:List Bool):
     Function.update (extras R O Y) Extra.output L=extras R L Y:=by
   funext k;cases k <;> simp [Function.update,extras]
 @[simp] theorem extras_symbols (R O:List Bool) (Y:List Symbol) (L:List Symbol):
     Function.update (extras R O Y) Extra.symbols L=extras R O L:=by
   funext k;cases k <;> simp [Function.update,extras]
 def stage (H:Machine) (p:Phase) (S:∀ k,List (H.tm.Γ k))
     (R O:List Bool) (Y:List Symbol) (aux:Aux:=(none,none)):(machine H).Cfg:=
   cfg (some (.inr p)) (H.tm.initialState,aux) (extendStore S (extras R O Y))

 theorem first_cons (H:Machine) (S:∀ k,List (H.tm.Γ k))
     (R O:List Bool) (Y:List Symbol) (b:Bool):
     step (code H) (stage H .first S (b::R) O Y)=
       some (stage H .second S R O Y (some b,none)):=by
   simp only [stage,cfg,step,code,stepAux,next,extendStore_inr,extras,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true]
   rw [right_update,extras_raw]
 theorem first_nil (H:Machine) (S:∀ k,List (H.tm.Γ k)) (O:List Bool) (Y:List Symbol):
     step (code H) (stage H .first S [] O Y)=some (stage H .input S [] O Y):=by
   simp only [stage,cfg,step,code,stepAux,next,extendStore_inr,extras,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false]
   rw [right_update,extras_raw]
 theorem second_cons (H:Machine) (S:∀ k,List (H.tm.Γ k))
     (R O:List Bool) (Y:List Symbol) (a b:Bool):
     step (code H) (stage H .second S (b::R) O Y (some a,none))=
       some (stage H .first S R O (decodePair a b::Y)):=by
   simp only [stage,cfg,step,code,stepAux,next,clearedNext,extendStore_inr,extras,
     List.head?_cons,List.tail_cons,Option.getD_some]
   rw [right_update,extras_raw,right_update,extras_symbols]
   simp only [extendStore_inr,extras]

 theorem input_cons (H:Machine) (S:∀ k,List (H.tm.Γ k))
     (R O:List Bool) (Y:List Symbol) (y:Symbol):
     step (code H) (stage H .input S R O (y::Y))=
       some (stage H .input (Function.update S H.tm.k₀ (H.inputAlphabet.symm y::S H.tm.k₀)) R O Y):=by
   simp only [stage,cfg,step,code,stepAux,next,clearedNext,extendStore_inr,extras,
     List.head?_cons,List.tail_cons,Option.isSome_some,Option.getD_some,cond_true]
   rw [right_update,extras_symbols,update_extend]
   simp only [extendStore_inl]
 theorem input_nil (H:Machine) (S:∀ k,List (H.tm.Γ k)) (R O:List Bool):
     step (code H) (stage H .input S R O [])=
       some (extendCfg Phase.output (none,none) (extras R O [])
         (cfg (some H.tm.main) H.tm.initialState S)):=by
   simp only [stage,cfg,step,code,stepAux,next,extendStore_inr,extras,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false,extendCfg]
   rw [right_update,extras_symbols]
 theorem output_cons (H:Machine) (S:∀ k,List (H.tm.Γ k))
     (R O:List Bool) (Y:List Symbol) (q:H.tm.Γ H.tm.k₁) (Q:List (H.tm.Γ H.tm.k₁))
     (h:S H.tm.k₁=q::Q):
     step (code H) (stage H .output S R O Y)=
       some (stage H .output (Function.update S H.tm.k₁ Q)
         (secondBit (H.outputAlphabet q)::firstBit (H.outputAlphabet q)::R) O Y):=by
   simp only [stage,cfg,step,code,stepAux,next,clearedNext,extendStore_inl,extendStore_inr,
     extras,h,List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,
     Option.getD_some,cond_true]
   rw [update_extend,right_update,extras_raw,right_update,extras_raw]
   simp only [extendStore_inr,extras]
 theorem output_nil (H:Machine) (S:∀ k,List (H.tm.Γ k))
     (R O:List Bool) (Y:List Symbol) (h:S H.tm.k₁=[]):
     step (code H) (stage H .output S R O Y)=some (stage H .finish S R O Y):=by
   simp only [stage,cfg,step,code,stepAux,next,extendStore_inl,extras,h,
     List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,cond_false]
   rw [update_extend]
   have hh:Function.update S H.tm.k₁ []=S:=by simpa only [h] using Function.update_eq_self H.tm.k₁ S
   rw [hh]
 theorem finish_cons (H:Machine) (S:∀ k,List (H.tm.Γ k))
     (R O:List Bool) (Y:List Symbol) (b:Bool):
     step (code H) (stage H .finish S (b::R) O Y)=some (stage H .finish S R (b::O) Y):=by
   simp only [stage,cfg,step,code,stepAux,next,clearedNext,extendStore_inr,extras,
     List.head?_cons,List.tail_cons,Option.isSome_some,Option.getD_some,cond_true]
   rw [right_update,extras_raw,right_update,extras_output]
   simp only [extendStore_inr,extras]
 theorem finish_nil (H:Machine) (S:∀ k,List (H.tm.Γ k)) (O:List Bool) (Y:List Symbol):
     step (code H) (stage H .finish S [] O Y)=
       some (cfg none (H.tm.initialState,(none,none)) (extendStore S (extras [] O Y))):=by
   simp only [stage,cfg,step,code,stepAux,next,extendStore_inr,extras,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false]
   rw [right_update,extras_raw]

end EdgeSublinearMWIS.Main.TernaryAdapter

end
end

section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackSpace

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

variable {K:Type} {Γ:K→ Type} {Λ σ:Type}

 def cost:Turing.TM2.Stmt Γ Λ σ→ ℕ
  | .push _ _ q => cost q + 1
  | .peek _ _ q => cost q + 1
  | .pop _ _ q => cost q + 1
  | .load _ q => cost q + 1
  | .branch _ q r => max (cost q) (cost r) + 1
  | .goto _ => 1
  | .halt => 1

 def space [Fintype K] (S:∀ k,List (Γ k)):ℕ:= ∑ k, (S k).length

 theorem space_update [Fintype K] [DecidableEq K] (S:∀ k,List (Γ k)) (k:K) (L:List (Γ k)):
    space (Function.update S k L) + (S k).length=space S + L.length:=by
  have heq:(fun j => (Function.update S k L j).length)=Function.update (fun j => (S j).length) k L.length:=by
    funext j
    by_cases h:j=k
    · subst j; simp
    · simp [Function.update,h]
  unfold space
  rw [heq,Finset.sum_update_of_mem (Finset.mem_univ k),Finset.sdiff_singleton_eq_erase]
  have hsum:=Finset.sum_erase_add (s:=Finset.univ) (fun j => (S j).length) (Finset.mem_univ k)
  omega

 theorem stepAux_space [Fintype K] [DecidableEq K] (q:Turing.TM2.Stmt Γ Λ σ)
    (v:σ) (S:∀ k,List (Γ k)):
    space (Turing.TM2.stepAux q v S).stk≤ space S + cost q:=by
  induction q generalizing v S with
  | push k f q ih =>
    have hh:=ih v (Function.update S k (f v::S k))
    have hu:=space_update S k (f v::S k)
    simp only [List.length_cons] at hu
    change space (Turing.TM2.stepAux q v (Function.update S k (f v::S k))).stk≤ space S + (cost q + 1)
    omega
  | peek k f q ih =>
    have hh:=ih (f v (S k).head?) S
    change space (Turing.TM2.stepAux q (f v (S k).head?) S).stk≤ space S + (cost q + 1)
    omega
  | pop k f q ih =>
    have hh:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    have hu:=space_update S k (S k).tail
    have hl:(S k).tail.length≤ (S k).length:=by simp only [List.length_tail]; omega
    change space (Turing.TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk≤ space S + (cost q + 1)
    omega
  | load f q ih =>
    have hh:=ih (f v) S
    change space (Turing.TM2.stepAux q (f v) S).stk≤ space S + (cost q + 1)
    omega
  | branch f q r ihq ihr =>
    change space (cond (f v) (Turing.TM2.stepAux q v S) (Turing.TM2.stepAux r v S)).stk≤ space S + (max (cost q) (cost r) + 1)
    cases hv:f v with
    | false => simp only [cond_false]; have hh:=ihr v S; have hm:=le_max_right (cost q) (cost r); omega
    | true => simp only [cond_true]; have hh:=ihq v S; have hm:=le_max_left (cost q) (cost r); omega
  | goto f => simp [Turing.TM2.stepAux,cost]
  | halt => simp [Turing.TM2.stepAux,cost]

 def bound (tm:Turing.FinTM2):ℕ:=Finset.univ.sup (fun l => cost (tm.m l))

 theorem cost_le_bound (tm:Turing.FinTM2) (l:tm.Λ):cost (tm.m l)≤ bound tm:=by
  unfold bound
  exact Finset.le_sup (f:=fun l => cost (tm.m l)) (Finset.mem_univ l)

 theorem initial_space (tm:Turing.FinTM2) (input:List (tm.Γ tm.k₀)):
    space (Turing.initList tm input).stk=input.length:=by
  have hlen (k:tm.K):((Turing.initList tm input).stk k).length=if k=tm.k₀ then input.length else 0:=by
    by_cases h:k=tm.k₀
    · subst k; simp [Turing.initList]
    · simp [Turing.initList,h]
  unfold space
  simp only [hlen]
  simp

 set_option backward.isDefEq.respectTransparency.types false in
 theorem step_space (tm:Turing.FinTM2) (c c':tm.Cfg) (h:tm.step c=some c'):
    space c'.stk≤ space c.stk + bound tm:=by
  letI:DecidableEq tm.K:=tm.decidableEqK
  change Turing.TM2.step tm.m c=some c' at h
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [Turing.FinTM2.step,Turing.TM2.step] at h
  | some l =>
    change some (Turing.TM2.stepAux (tm.m l) v S)=some c' at h
    have heq:=Option.some.inj h
    rw [← heq]
    exact (stepAux_space (tm.m l) v S).trans (Nat.add_le_add_left (cost_le_bound tm l) _)

 def run (tm:Turing.FinTM2) (start:tm.Cfg):ℕ→ Option tm.Cfg
  | 0 => some start
  | t + 1 => (run tm start t).bind tm.step

 theorem run_space (tm:Turing.FinTM2) (start:tm.Cfg) (t:ℕ) (c:tm.Cfg)
    (h:run tm start t=some c):space c.stk≤ space start.stk + bound tm * t:=by
  induction t generalizing c with
  | zero => simp only [run,Option.some.injEq] at h; subst c; simp
  | succ t ih =>
    cases he:run tm start t with
    | none => simp only [run,he,Option.bind_none,reduceCtorEq] at h
    | some prev =>
      have hstep:tm.step prev=some c:=by simpa only [run,he,Option.bind_some] using h
      have hi:=ih prev he
      have hs:=step_space tm prev c hstep
      rw [Nat.mul_succ]
      omega

 theorem input_run_space (tm:Turing.FinTM2) (input:List (tm.Γ tm.k₀)) (t:ℕ) (c:tm.Cfg)
    (h:run tm (Turing.initList tm input) t=some c):space c.stk≤ input.length + bound tm * t:=by
  simpa only [initial_space] using run_space tm (Turing.initList tm input) t c h

 theorem stack_length_le_space [Fintype K] (S:∀ k,List (Γ k)) (k:K):(S k).length≤ space S:=by
  unfold space
  exact Finset.single_le_sum (f:=fun j => (S j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

end EdgeSublinearMWIS.Main.StackSpace

end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Phase where | out | into | finish deriving Fintype,DecidableEq

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def onlyStack {κ:Type} [DecidableEq κ] {Γ:κ→ Type} (k:κ) (L:List (Γ k)):∀j,List (Γ j):=
   Function.update (fun _ => []) k L
 @[simp] theorem onlyStack_self {κ:Type} [DecidableEq κ] {Γ:κ→ Type} (k:κ) (L:List (Γ k)):onlyStack k L k=L:=by simp [onlyStack]
 theorem onlyStack_nil {κ:Type} [DecidableEq κ] {Γ:κ→ Type} (k:κ):onlyStack k ([]:List (Γ k))=(fun _ => []):=by simp [onlyStack,Function.update_eq_self]
 theorem onlyStack_update {κ:Type} [DecidableEq κ] {Γ:κ→ Type} (k:κ) (L R:List (Γ k)):
     Function.update (onlyStack k L) k R=onlyStack k R:=by simp [onlyStack,Function.update_idem]

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.TernaryAdapter
open Turing.TM2 ProgramComposition RawStack Lax759944.BinaryWordEncoding
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem finish_loop (H:Machine) (S:∀ k,List (H.tm.Γ k))
     (R O:List Bool) (Y:List Symbol):
     run (code H) (stage H .finish S R O Y) (R.length+1)=
       some (cfg none (H.tm.initialState,(none,none)) (extendStore S (extras [] (R.reverse++O) Y))):=by
   induction R generalizing O with
   | nil => simpa only [List.length_nil,Nat.zero_add,run_one,List.reverse_nil,List.nil_append] using finish_nil H S O Y
   | cons b R ih =>
     rw [List.length_cons,run_first,finish_cons,Option.bind_some]
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih (b::O)

 theorem input_loop (H:Machine) (L:List (H.tm.Γ H.tm.k₀)) (Y:List Symbol):
     run (code H) (stage H .input (onlyStack H.tm.k₀ L) [] [] Y) (Y.length+1)=
       some (extendCfg Phase.output (none,none) (extras [] [] [])
         (cfg (some H.tm.main) H.tm.initialState
           (onlyStack H.tm.k₀ ((Y.map H.inputAlphabet.symm).reverse++L)))):=by
   induction Y generalizing L with
   | nil => simpa only [List.length_nil,Nat.zero_add,run_one,List.map_nil,List.reverse_nil,List.nil_append] using input_nil H (onlyStack H.tm.k₀ L) [] []
   | cons y Y ih =>
     rw [List.length_cons,run_first,input_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using ih (H.inputAlphabet.symm y::L)

 theorem decode_loop (H:Machine) (S:∀ k,List (H.tm.Γ k))
     (xs:List Symbol) (O:List Bool) (Y:List Symbol):
     run (code H) (stage H .first S (binarySymbols xs) O Y) (2*xs.length+1)=
       some (stage H .input S [] O (xs.reverse++Y)):=by
   induction xs generalizing Y with
   | nil => simpa only [binarySymbols,List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,run_one,List.reverse_nil,List.nil_append] using first_nil H S O Y
   | cons x xs ih =>
     have htwo:run (code H)
         (stage H .first S (firstBit x::secondBit x::binarySymbols xs) O Y) 2=
         some (stage H .first S (binarySymbols xs) O (x::Y)):=by
       rw [show (2:ℕ)=1+1 by rfl,run_add,run_one,first_cons,Option.bind_some,run_one,second_cons,decode_symbol]
     have hh:=run_trans (code H) _ _ _ 2 (2*xs.length+1) htwo (ih (x::Y))
     have he:2*(xs.length+1)+1=2+(2*xs.length+1):=by omega
     simpa only [binarySymbols,List.flatMap_cons,symbolBits,List.cons_append,List.nil_append,
       List.length_cons,he,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

 theorem output_loop (H:Machine) (xs:List Symbol) (R:List Bool):
     run (code H) (stage H .output (onlyStack H.tm.k₁ (xs.map H.outputAlphabet.symm)) R [] []) (xs.length+1)=
       some (stage H .finish (fun _ => []) ((binarySymbols xs).reverse++R) [] []):=by
   induction xs generalizing R with
   | nil =>
     have hh:=output_nil H (onlyStack H.tm.k₁ []) R [] [] (by simp)
     simpa only [List.map_nil,List.length_nil,Nat.zero_add,run_one,onlyStack_nil,binarySymbols,List.flatMap_nil,List.reverse_nil,List.nil_append] using hh
   | cons x xs ih =>
     have hs:=output_cons H (onlyStack H.tm.k₁ ((x::xs).map H.outputAlphabet.symm)) R [] []
       (H.outputAlphabet.symm x) (xs.map H.outputAlphabet.symm) (by simp)
     rw [onlyStack_update] at hs
     simp only [Equiv.apply_symm_apply] at hs
     rw [List.length_cons,run_first,hs,Option.bind_some]
     simpa only [binarySymbols,List.flatMap_cons,List.reverse_append,symbolBits,List.reverse_cons,
       List.reverse_nil,List.nil_append,List.append_assoc,List.singleton_append,List.cons_append] using ih (secondBit x::firstBit x::R)

end EdgeSublinearMWIS.Main.TernaryAdapter

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem haltList_store (tm:Turing.FinTM2) (L:List (tm.Γ tm.k₁)):
     (Turing.haltList tm L).stk=onlyStack tm.k₁ L:=by
   funext k
   by_cases h:k=tm.k₁
   · subst k; simp [Turing.haltList,onlyStack]
   · simp [Turing.haltList,onlyStack,Function.update,h]

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem cfg_eq {κ Λ σ:Type} {Γ:κ→ Type} {c d:Cfg Γ Λ σ}
     (hl:c.l=d.l) (hv:c.var=d.var) (hs:c.stk=d.stk):c=d:=by
   cases c; cases d; simp_all

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.TernaryAdapter
open Turing.TM2 ProgramComposition RawStack Lax759944.BinaryWordEncoding
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem adapter_init (H:Machine) (input:List Bool):
     Turing.initList (machine H) input=stage H .first (fun _ => []) input [] []:=by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => simp [Turing.initList,machine,stage,cfg,extendStore]
   | inr k => cases k <;> simp [Turing.initList,machine,stage,cfg,extendStore,extras]
 theorem adapter_halt (H:Machine) (output:List Bool):
     cfg (Γ:=Alphabet H) (Λ:=Label H) none (H.tm.initialState,(none,none))
       (extendStore (fun _ => []) (extras [] output []))=Turing.haltList (machine H) output:=by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => simp [Turing.haltList,machine,cfg,extendStore]
   | inr k => cases k <;> simp [Turing.haltList,machine,cfg,extendStore,extras]
 theorem input_entry (H:Machine) (xs:List Symbol):
     run (code H) (stage H .input (fun _ => []) [] [] xs.reverse) (xs.length+1)=
       some (extendCfg Phase.output (none,none) (extras [] [] [])
         (Turing.initList H.tm (xs.map H.inputAlphabet.symm))):=by
   have hh:=input_loop H [] xs.reverse
   simp only [onlyStack_nil,List.length_reverse,List.map_reverse,List.reverse_reverse,List.append_nil] at hh
   have he:cfg (some H.tm.main) H.tm.initialState (onlyStack H.tm.k₀ (xs.map H.inputAlphabet.symm))=
       Turing.initList H.tm (xs.map H.inputAlphabet.symm):=by
     apply cfg_eq
     case hl => rfl
     case hv => rfl
     funext k
     by_cases h:k=H.tm.k₀
     · subst k; simp [cfg,onlyStack,Turing.initList,Function.update]
     · simp [cfg,onlyStack,Turing.initList,Function.update,h]
   rw [he] at hh
   exact hh
 theorem output_exit (H:Machine) (xs:List Symbol):
     run (code H)
       (extendCfg Phase.output (none,none) (extras [] [] [])
         (Turing.haltList H.tm (xs.map H.outputAlphabet.symm)))
       (3*xs.length+2)=some (Turing.haltList (machine H) (binarySymbols xs)):=by
   have hs:extendCfg Phase.output (none,none) (extras [] [] [])
         (Turing.haltList H.tm (xs.map H.outputAlphabet.symm))=
       stage H .output (onlyStack H.tm.k₁ (xs.map H.outputAlphabet.symm)) [] [] []:=by
     apply cfg_eq
     case hl => rfl
     case hv => rfl
     funext k
     cases k with
     | inl k =>
       by_cases h:k=H.tm.k₁
       · subst k; simp [Turing.haltList,extendCfg,stage,cfg,extendStore,onlyStack,Function.update]
       · simp [Turing.haltList,extendCfg,stage,cfg,extendStore,onlyStack,Function.update,h]
     | inr k => rfl
   have h₁:=output_loop H xs []
   simp only [List.append_nil] at h₁
   have h₂:=finish_loop H (fun _ => []) (binarySymbols xs).reverse [] []
   simp only [List.length_reverse,binarySymbols_length,List.reverse_reverse,List.append_nil] at h₂
   rw [adapter_halt] at h₂
   have hh:=run_trans (code H) _ _ _ (xs.length+1) (2*xs.length+1) h₁ h₂
   rw [hs]
   have hc:xs.length+1+(2*xs.length+1)=3*xs.length+2:=by omega
   rw [hc] at hh
   exact hh

 theorem adapter_run (H:Machine) (xs ys:List Symbol) (t:ℕ)
     (h:run H.tm.m (Turing.initList H.tm (xs.map H.inputAlphabet.symm)) t=
       some (Turing.haltList H.tm (ys.map H.outputAlphabet.symm))):
     run (code H) (Turing.initList (machine H) (binarySymbols xs))
       (t+3*xs.length+3*ys.length+4)=
       some (Turing.haltList (machine H) (binarySymbols ys)):=by
   have h₁:=decode_loop H (fun _ => []) xs [] []
   simp only [List.append_nil] at h₁
   have h₂:=input_entry H xs
   have h₃:=run_extend Phase.output H.tm.m (code H) (fun _ => rfl) _ _
     ((none,none):Aux) (extras [] [] []) t h
   have h₄:=output_exit H ys
   have h₁₂:=run_trans (code H) _ _ _ _ _ h₁ h₂
   have h₁₂₃:=run_trans (code H) _ _ _ _ _ h₁₂ h₃
   have hh:=run_trans (code H) _ _ _ _ _ h₁₂₃ h₄
   rw [adapter_init]
   have hc:(2*xs.length+1+(xs.length+1))+t+(3*ys.length+2)=t+3*xs.length+3*ys.length+4:=by omega
   rw [hc] at hh
   exact hh

end EdgeSublinearMWIS.Main.TernaryAdapter

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem spaceRun_eq (tm:Turing.FinTM2) (c:tm.Cfg) (t:ℕ):
     StackSpace.run tm c t=RawStack.run tm.m c t:=by
   induction t with
   | zero => rfl
   | succ t ih => simp only [StackSpace.run,RawStack.run,ih]; rfl

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.TernaryAdapter
open Turing.TM2 ProgramComposition RawStack Lax759944.BinaryWordEncoding
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem source_run (H:Machine) (xs ys:List Symbol) (T:ℕ)
     (h:Nonempty (Turing.TM2OutputsInTime H.tm (xs.map H.inputAlphabet.symm)
       (some (ys.map H.outputAlphabet.symm)) T)):
     ∃ t,t≤ T∧ run H.tm.m (Turing.initList H.tm (xs.map H.inputAlphabet.symm)) t=
       some (Turing.haltList H.tm (ys.map H.outputAlphabet.symm)):=by
   obtain ⟨h⟩:=h
   refine ⟨h.steps,h.steps_le_m,?_⟩
   rw [run_iter]
   exact h.evals_in_steps

 theorem adapter_correct (H:Machine) (hΓ:∀ k,Finite (H.tm.Γ k))
     (xs ys:List Symbol) (T:ℕ)
     (h:Nonempty (Turing.TM2OutputsInTime H.tm (xs.map H.inputAlphabet.symm)
       (some (ys.map H.outputAlphabet.symm)) T)):
     Runs (program H hΓ) (binarySymbols xs) (binarySymbols ys)
       (T+3*xs.length+3*ys.length+4):=by
   obtain ⟨t,ht,hr⟩:=source_run H xs ys T h
   have hh:=adapter_run H xs ys t hr
   obtain ⟨hh⟩:=outputs (tm:=machine H) (binarySymbols xs) (binarySymbols ys) _ hh
   change Nonempty (Turing.TM2OutputsInTime (machine H) ((binarySymbols xs).map id)
     (some ((binarySymbols ys).map id)) _)
   simp only [List.map_id]
   exact ⟨{hh with steps_le_m:=hh.steps_le_m.trans (by omega)}⟩

 theorem source_output_length (H:Machine) (xs ys:List Symbol) (T:ℕ)
     (h:Nonempty (Turing.TM2OutputsInTime H.tm (xs.map H.inputAlphabet.symm)
       (some (ys.map H.outputAlphabet.symm)) T)):
     ys.length≤ xs.length+StackSpace.bound H.tm*T:=by
   obtain ⟨t,ht,hr⟩:=source_run H xs ys T h
   have hr':StackSpace.run H.tm (Turing.initList H.tm (xs.map H.inputAlphabet.symm)) t=
       some (Turing.haltList H.tm (ys.map H.outputAlphabet.symm)):=by rw [spaceRun_eq]; exact hr
   have hs:=StackSpace.input_run_space H.tm (xs.map H.inputAlphabet.symm) t _ hr'
   have hl:=StackSpace.stack_length_le_space
     (Turing.haltList H.tm (ys.map H.outputAlphabet.symm)).stk H.tm.k₁
   simp only [haltList_store,onlyStack_self,List.length_map] at hl
   rw [haltList_store] at hs
   simp only [List.length_map] at hs
   have hh:=hl.trans hs
   have hm:=Nat.mul_le_mul_left (StackSpace.bound H.tm) ht
   omega

 theorem adapter_linear (H:Machine) (hΓ:∀ k,Finite (H.tm.Γ k)):
     ∃ K:ℕ,0 < K∧ ∀ (xs ys:List Symbol) (T:ℕ),
       Nonempty (Turing.TM2OutputsInTime H.tm (xs.map H.inputAlphabet.symm)
         (some (ys.map H.outputAlphabet.symm)) T)→
       Runs (program H hΓ) (binarySymbols xs) (binarySymbols ys) (K*(T+xs.length+1)):=by
   refine ⟨3*StackSpace.bound H.tm+8,by omega,?_⟩
   intro xs ys T h
   have hl:=source_output_length H xs ys T h
   obtain ⟨hr⟩:=adapter_correct H hΓ xs ys T h
   refine ⟨{hr with steps_le_m:=hr.steps_le_m.trans ?_}⟩
   nlinarith only [hl,Nat.zero_le (StackSpace.bound H.tm*xs.length),Nat.zero_le (StackSpace.bound H.tm)]

end EdgeSublinearMWIS.Main.TernaryAdapter

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open Lax759944.BinaryWordEncoding Polynomial TernaryAdapter
open Lax759944Proofs.RamToTM Lax759944Proofs

 theorem uniform_bit_simulation:∃ q:ℕ,0<q∧ ∀ p:Lax808846.Ram.Program,
    ∃ (E:Program) (W:Polynomial ℕ) (K:ℕ),0<K∧
      (∀ n,2*n+1≤ W.eval n)∧ ∀ (xs ys:List ℕ) (t:ℕ),
      Lax759944.RamPolytime.FitsInWords (2*bitSize xs+1) ((xs.length::xs)++ys)→
      Lax808846.Ram.RunsTo (W.eval (bitSize xs)) p (xs.length::xs) ys t→
      Runs E (wordBits xs) (wordBits ys) (K*(bitSize xs+t+1)^q):=by
  obtain ⟨q,hq,hbound⟩:=fixed_width_universal_exponent
  refine ⟨max q 1,by omega,?_⟩
  intro p
  obtain ⟨H,W,hΓ,hW,hH⟩:=TapeRamGenericTime.genericTime_of_lowering_finite_explicit
    TapeRamNativeLowering.lower TapeRamNativeLowering.runsTo Encoding.length_le_bitSize p (2*X+1)
  obtain ⟨A,hA,hAdapter⟩:=adapter_linear H hΓ
  obtain ⟨B,hB,hBbound⟩:=hbound (CellToMicrocode.compile (TapeRamNativeLowering.lower p))
  refine ⟨program H hΓ,W,A*(B+2),by positivity,?_,?_⟩
  · intro n; simpa using hW n
  · intro xs ys t hfits hrun
    have hr:=hH xs ys t (by simpa using hfits) hrun
    have ha:=hAdapter (encode xs) (encode ys) _ hr
    obtain ⟨ha⟩:=ha
    refine ⟨{ha with steps_le_m:=ha.steps_le_m.trans ?_}⟩
    have hb:=hBbound (bitSize xs+t)
    have hp:(bitSize xs+t+1)^q≤ (bitSize xs+t+1)^(max q 1):=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hn:bitSize xs+t+1≤ (bitSize xs+t+1)^(max q 1):=
      le_self_pow (by omega) (by omega)
    change A*(_+(encode xs).length+1)≤ A*(B+2)*(bitSize xs+t+1)^max q 1
    change A*(_+bitSize xs+1)≤ _
    have hb':=hb.trans (Nat.mul_le_mul_left B hp)
    nlinarith only [hb',hn]

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Extra where | raw | context | count | consume | temp deriving Fintype,DecidableEq
 inductive CallPhase where | count | context | out | into | emitContext | prefix deriving Fintype,DecidableEq

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

theorem solution:∃ (q:ℕ),
  0 < q∧
    ∀ (p:Lax808846.Ram.Program),
      ∃ (E:EdgeSublinearMWIS.Main.Program) (W:Polynomial ℕ) (K:ℕ),
        0 < K∧
          (∀ (n:ℕ),2 * n + 1≤ Polynomial.eval n W)∧
            ∀ (xs ys:List ℕ) (t:ℕ),
              Lax759944.RamPolytime.FitsInWords (2 * Lax759944.BinaryWordEncoding.bitSize xs + 1)
                  (xs.length::xs ++ ys)→
                Lax808846.Ram.RunsTo (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize xs) W) p (xs.length::xs)
                    ys t→
                  EdgeSublinearMWIS.Main.Runs E (EdgeSublinearMWIS.Main.RamBridge.wordBits xs)
                    (EdgeSublinearMWIS.Main.RamBridge.wordBits ys)
                    (K * (Lax759944.BinaryWordEncoding.bitSize xs + t + 1) ^ q):= @EdgeSublinearMWIS.Main.RamBridge.uniform_bit_simulation

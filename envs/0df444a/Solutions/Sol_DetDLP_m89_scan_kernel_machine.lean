-- Prove2me | solution 1 for DetDLP.m89_scan_kernel_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T22:02:51.359671+00:00
-- url     : https://prove2.me/submissions/f02a3b58-bef6-4039-afe6-304d83c65aa6

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_M89_ScanArithmetic
import Definitions.Def_DetDLP_M89_BitCompiler
import Definitions.Def_DetDLP_M89_CompileSpace

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DetDLP.M89ScanKernel

open DetDLP
open DetDLP.M89Scan
open OAI.Algorithms
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-! ## Section 1: Machine layout, `Spec` framework, and `Atom` evaluation helpers -/

section LayoutAndSpec

abbrev R : ℕ := 16
abbrev S : ℕ := 28

abbrev rVal     : Fin R := ⟨0, by decide⟩
abbrev rPres    : Fin R := ⟨1, by decide⟩
abbrev rVal2    : Fin R := ⟨2, by decide⟩
abbrev rPres2   : Fin R := ⟨3, by decide⟩
abbrev rCarry   : Fin R := ⟨4, by decide⟩
abbrev rBit     : Fin R := ⟨5, by decide⟩
abbrev rCmp     : Fin R := ⟨6, by decide⟩
abbrev rFlag    : Fin R := ⟨7, by decide⟩
abbrev rLoop    : Fin R := ⟨8, by decide⟩
abbrev rFound   : Fin R := ⟨9, by decide⟩
abbrev rEq      : Fin R := ⟨10, by decide⟩
abbrev rHasR    : Fin R := ⟨11, by decide⟩
abbrev rHasNext : Fin R := ⟨12, by decide⟩
abbrev rTmp1    : Fin R := ⟨13, by decide⟩
abbrev rTmp2    : Fin R := ⟨14, by decide⟩
abbrev rTmp3    : Fin R := ⟨15, by decide⟩

abbrev sIn      : Fin S := ⟨0, by decide⟩
abbrev sOut     : Fin S := ⟨1, by decide⟩
abbrev sFs      : Fin S := ⟨2, by decide⟩
abbrev sUs      : Fin S := ⟨3, by decide⟩
abbrev sUsBak   : Fin S := ⟨4, by decide⟩
abbrev sP       : Fin S := ⟨5, by decide⟩
abbrev sN       : Fin S := ⟨6, by decide⟩
abbrev sAns     : Fin S := ⟨7, by decide⟩
abbrev sR       : Fin S := ⟨8, by decide⟩
abbrev sRNext   : Fin S := ⟨9, by decide⟩
abbrev sRp      : Fin S := ⟨10, by decide⟩
abbrev sQ       : Fin S := ⟨11, by decide⟩
abbrev sE2      : Fin S := ⟨12, by decide⟩
abbrev sW       : Fin S := ⟨13, by decide⟩
abbrev sU       : Fin S := ⟨14, by decide⟩
abbrev sPowAcc  : Fin S := ⟨15, by decide⟩
abbrev sPowBase : Fin S := ⟨16, by decide⟩
abbrev sPowExp  : Fin S := ⟨17, by decide⟩
abbrev sMulA    : Fin S := ⟨18, by decide⟩
abbrev sMulB    : Fin S := ⟨19, by decide⟩
abbrev sMulAcc  : Fin S := ⟨20, by decide⟩
abbrev sDivN    : Fin S := ⟨21, by decide⟩
abbrev sDivD    : Fin S := ⟨22, by decide⟩
abbrev sDivQ    : Fin S := ⟨23, by decide⟩
abbrev sDivR    : Fin S := ⟨24, by decide⟩
abbrev sTmp1    : Fin S := ⟨25, by decide⟩
abbrev sTmp2    : Fin S := ⟨26, by decide⟩
abbrev sTmp3    : Fin S := ⟨27, by decide⟩

abbrev SCmd := StructuredCalls.Cmd R S
abbrev SState := StructuredCalls.State R S

@[inline] def mkAtom (a : StructuredProgram.Atom R S) : SCmd := .base (.atom a)
@[inline] def mkSkip : SCmd := .base .skip
@[inline] def mkSeq (c₁ c₂ : SCmd) : SCmd := .seq c₁ c₂
@[inline] def mkSeqList : List SCmd → SCmd
  | [] => mkSkip
  | [c] => c
  | c :: cs => mkSeq c (mkSeqList cs)
@[inline] def mkIte (test : Fin R) (yes no : SCmd) : SCmd := .ite test yes no
@[inline] def mkWhile (test : Fin R) (body : SCmd) : SCmd := .while test body

/-- Determinism of bit-program traces terminating at `pc = none`. -/
theorem bitTrace_det {r s l : ℕ} (p : BitProgram.Program r s l)
    {n₁ n₂ : ℕ} {a b₁ b₂ : BitProgram.Cfg r s l}
    (h₁ : BitProgram.Trace p n₁ a b₁) (h₂ : BitProgram.Trace p n₂ a b₂)
    (hb₁ : b₁.pc = none) (hb₂ : b₂.pc = none) :
    n₁ = n₂ ∧ b₁ = b₂ := by
  induction h₁ generalizing n₂ with
  | refl a =>
      cases h₂ with
      | refl => exact ⟨rfl, rfl⟩
      | cons hs _ => simp [BitProgram.step, hb₁] at hs
  | @cons m x y z hs₁ ht₁ ih =>
      cases h₂ with
      | refl => simp [BitProgram.step, hb₂] at hs₁
      | @cons m' _ y' _ hs₂ ht₂ =>
          have hy : y = y' := Option.some.inj (hs₁.symm.trans hs₂)
          subst hy
          obtain ⟨hn, hz⟩ := ih ht₂ hb₁
          exact ⟨congrArg Nat.succ hn, hz⟩

theorem base_eval_det {r s : ℕ} {c : StructuredProgram.Cmd r s} {n₁ n₂ : ℕ}
    {a b₁ b₂ : StructuredProgram.State r s}
    (h₁ : StructuredProgram.Eval c n₁ a b₁) (h₂ : StructuredProgram.Eval c n₂ a b₂) :
    n₁ = n₂ ∧ b₁ = b₂ := by
  induction h₁ generalizing n₂ b₂ with
  | skip => cases h₂; exact ⟨rfl, rfl⟩
  | atom => cases h₂; exact ⟨rfl, rfl⟩
  | seq _ _ ihf ihs =>
      cases h₂ with
      | seq hf₂ hs₂ =>
          obtain ⟨hn₁, hb₁⟩ := ihf hf₂
          subst hn₁; subst hb₁
          obtain ⟨hn₂, hb₂⟩ := ihs hs₂
          exact ⟨congrArg _ hn₂, hb₂⟩
  | ite_true ht _ ih =>
      cases h₂ with
      | ite_true _ hy₂ =>
          obtain ⟨hn, hb⟩ := ih hy₂
          exact ⟨congrArg Nat.succ hn, hb⟩
      | ite_false hf _ => rw [ht] at hf; cases hf
  | ite_false hf _ ih =>
      cases h₂ with
      | ite_true ht _ => rw [hf] at ht; cases ht
      | ite_false _ hn₂ =>
          obtain ⟨hn, hb⟩ := ih hn₂
          exact ⟨congrArg Nat.succ hn, hb⟩
  | while_false hf =>
      cases h₂ with
      | while_false _ => exact ⟨rfl, rfl⟩
      | while_true ht _ _ => rw [hf] at ht; cases ht
  | while_true ht _ _ ihb ihw =>
      cases h₂ with
      | while_false hf => rw [ht] at hf; cases hf
      | while_true _ hb₂ hw₂ =>
          obtain ⟨hn₁, hmid⟩ := ihb hb₂
          subst hn₁; subst hmid
          obtain ⟨hn₂, hres⟩ := ihw hw₂
          subst hn₂; exact ⟨rfl, hres⟩

theorem eval_det {r s : ℕ} {c : StructuredCalls.Cmd r s} {n₁ n₂ : ℕ}
    {a b₁ b₂ : StructuredCalls.State r s}
    (h₁ : StructuredCalls.Eval c n₁ a b₁) (h₂ : StructuredCalls.Eval c n₂ a b₂) :
    n₁ = n₂ ∧ b₁ = b₂ := by
  induction h₁ generalizing n₂ b₂ with
  | base he₁ =>
      cases h₂ with
      | base he₂ => exact base_eval_det he₁ he₂
  | call p ht₁ =>
      cases h₂ with
      | call _ ht₂ =>
          obtain ⟨hn, hcfg⟩ := bitTrace_det p ht₁ ht₂ rfl rfl
          exact ⟨hn, by simpa using congrArg StructuredProgram.State.ofCfg hcfg⟩
  | seq _ _ ihf ihs =>
      cases h₂ with
      | seq hf₂ hs₂ =>
          obtain ⟨hn₁, hb₁⟩ := ihf hf₂
          subst hn₁; subst hb₁
          obtain ⟨hn₂, hb₂⟩ := ihs hs₂
          exact ⟨congrArg _ hn₂, hb₂⟩
  | ite_true ht _ ih =>
      cases h₂ with
      | ite_true _ hy₂ =>
          obtain ⟨hn, hb⟩ := ih hy₂
          exact ⟨congrArg Nat.succ hn, hb⟩
      | ite_false hf _ => rw [ht] at hf; cases hf
  | ite_false hf _ ih =>
      cases h₂ with
      | ite_true ht _ => rw [hf] at ht; cases ht
      | ite_false _ hn₂ =>
          obtain ⟨hn, hb⟩ := ih hn₂
          exact ⟨congrArg Nat.succ hn, hb⟩
  | while_false hf =>
      cases h₂ with
      | while_false _ => exact ⟨rfl, rfl⟩
      | while_true ht _ _ => rw [hf] at ht; cases ht
  | while_true ht _ _ ihb ihw =>
      cases h₂ with
      | while_false hf => rw [ht] at hf; cases hf
      | while_true _ hb₂ hw₂ =>
          obtain ⟨hn₁, hmid⟩ := ihb hb₂
          subst hn₁; subst hmid
          obtain ⟨hn₂, hres⟩ := ihw hw₂
          subst hn₂; exact ⟨rfl, hres⟩

/-- Compositional execution + uniform all-prefix stack-length bound for `StructuredCalls.Cmd`. -/
def Spec {r s : ℕ} (inS outS : Fin s) (c : StructuredCalls.Cmd r s)
    (a b : StructuredCalls.State r s) (n B : ℕ) : Prop :=
  StructuredCalls.Eval c n a b ∧
  ∀ k mid, k ≤ n →
    BitProgram.Trace (StructuredCalls.compiled c inS outS) k
      (a.withPC (some (StructuredCalls.compiled c inS outS).entry)) mid →
    ∀ i, (mid.stacks i).length ≤ B

namespace Spec

theorem of_eval_local {r s : ℕ} {inS outS : Fin s} {c : StructuredCalls.Cmd r s}
    {a b : StructuredCalls.State r s} {n B : ℕ}
    (he : StructuredCalls.Eval c n a b)
    (hb : BitProgram.stackBits a.stacks + n ≤ B) :
    Spec inS outS c a b n B := by
  refine ⟨he, fun k mid hk htr i => ?_⟩
  have hloc := StructuredSpace.local_stack_bound (StructuredCalls.compiled c inS outS)
    (a := a.withPC (some (StructuredCalls.compiled c inS outS).entry))
    (steps := n) (initialBound := BitProgram.stackBits a.stacks) le_rfl k mid hk htr i
  exact hloc.trans hb

theorem mono {r s : ℕ} {inS outS : Fin s} {c : StructuredCalls.Cmd r s}
    {a b : StructuredCalls.State r s} {n B₁ B₂ : ℕ}
    (h : Spec inS outS c a b n B₁) (hle : B₁ ≤ B₂) :
    Spec inS outS c a b n B₂ :=
  ⟨h.1, fun k mid hk htr i => (h.2 k mid hk htr i).trans hle⟩

theorem skip {r s : ℕ} (inS outS : Fin s) (a : StructuredCalls.State r s) {B : ℕ}
    (ha : BitProgram.stackBits a.stacks ≤ B) :
    Spec inS outS (.base .skip) a a 0 B :=
  of_eval_local (.base (.skip a)) (by simpa using ha)

theorem atom {r s : ℕ} (inS outS : Fin s) (op : StructuredProgram.Atom r s)
    (a : StructuredCalls.State r s) {B : ℕ}
    (ha : BitProgram.stackBits a.stacks + 1 ≤ B) :
    Spec inS outS (.base (.atom op)) a (op.eval a) 1 B :=
  of_eval_local (.base (.atom op a)) ha

theorem seq {r s : ℕ} {inS outS : Fin s} {c₁ c₂ : StructuredCalls.Cmd r s}
    {a b c : StructuredCalls.State r s} {n m B : ℕ}
    (h₁ : Spec inS outS c₁ a b n B) (h₂ : Spec inS outS c₂ b c m B) :
    Spec inS outS (.seq c₁ c₂) a c (n + m) B := by
  refine ⟨.seq h₁.1 h₂.1, ?_⟩
  exact StructuredSpace.sequence_stack_bound h₁.1 h₂.1 inS outS h₁.2 h₂.2
    (StructuredCalls.compiled (.seq c₁ c₂) inS outS)
    (StructuredCalls.siteAddress (.seq c₁ c₂))
    (StructuredCalls.exitAddress (.seq c₁ c₂))
    (StructuredCalls.compiled_site (.seq c₁ c₂) inS outS)

theorem ite_true {r s : ℕ} {inS outS : Fin s} {test : Fin r}
    {yes no : StructuredCalls.Cmd r s} {a b : StructuredCalls.State r s} {n B : ℕ}
    (ht : a.regs test = true) (h : Spec inS outS yes a b n B) :
    Spec inS outS (.ite test yes no) a b (n + 1) B := by
  refine ⟨.ite_true ht h.1, ?_⟩
  exact StructuredSpace.conditional_true_stack_bound ht h.1 inS outS h.2
    (StructuredCalls.compiled (.ite test yes no) inS outS)
    (StructuredCalls.siteAddress (.ite test yes no))
    (StructuredCalls.exitAddress (.ite test yes no))
    (StructuredCalls.compiled_site (.ite test yes no) inS outS)

theorem ite_false {r s : ℕ} {inS outS : Fin s} {test : Fin r}
    {yes no : StructuredCalls.Cmd r s} {a b : StructuredCalls.State r s} {n B : ℕ}
    (ht : a.regs test = false) (h : Spec inS outS no a b n B) :
    Spec inS outS (.ite test yes no) a b (n + 1) B := by
  refine ⟨.ite_false ht h.1, ?_⟩
  exact StructuredSpace.conditional_false_stack_bound ht h.1 inS outS h.2
    (StructuredCalls.compiled (.ite test yes no) inS outS)
    (StructuredCalls.siteAddress (.ite test yes no))
    (StructuredCalls.exitAddress (.ite test yes no))
    (StructuredCalls.compiled_site (.ite test yes no) inS outS)

theorem «while» {r s : ℕ} (inS outS : Fin s) (body : StructuredCalls.Cmd r s) (test : Fin r)
    (I : StructuredCalls.State r s → Prop) (bound : ℕ)
    (hinit : ∀ x, I x → ∀ i, (x.stacks i).length ≤ bound)
    (hstep : ∀ x, I x → x.regs test = true →
      ∃ n y, Spec inS outS body x y n bound ∧ I y)
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval (.while test body) steps a b) (ha : I a) :
    Spec inS outS (.while test body) a b steps bound := by
  refine ⟨heval, ?_⟩
  refine StructuredSpace.loop_stack_bound body test inS outS I bound hinit ?_ ?_ heval ha
  · intro n x y hxy hx ht
    obtain ⟨n', y', hsp, hy⟩ := hstep x hx ht
    obtain ⟨_, rfl⟩ := eval_det hxy hsp.1
    exact hy
  · intro n x y hxy hx ht
    obtain ⟨n', y', hsp, _⟩ := hstep x hx ht
    obtain ⟨rfl, rfl⟩ := eval_det hxy hsp.1
    exact hsp.2

theorem to_runsWithin {r s : ℕ} {inS outS : Fin s} {c : StructuredCalls.Cmd r s}
    {input output : List Bool} {b : StructuredCalls.State r s} {n B : ℕ} {τ σ : ℝ}
    (h : Spec inS outS c (StructuredProgram.ioState inS input) b n B)
    (hout : b.stacks outS = output)
    (ht : ((7 * (n + 1) : ℕ) : ℝ) ≤ τ)
    (hs : ((s * (B + input.length + 15) : ℕ) : ℝ) ≤ σ) :
    RunsWithin (GuardedCompiler.primitive (StructuredCalls.compiled c inS outS)) outS
      input output τ σ := by
  have htr : BitProgram.Trace (StructuredCalls.compiled c inS outS) (n + 1)
      (BitProgram.initial (StructuredCalls.compiled c inS outS) input) (b.withPC none) :=
    StructuredCalls.compiled_halt_trace h.1 inS outS
  have hstk := StructuredSpace.compiled_halt_stack_bound h.1 inS outS h.2
  exact CompileSpace.compile_runsWithin_of_le (StructuredCalls.compiled c inS outS)
    htr rfl hout hstk ht hs

end Spec

/-- Single-atom evaluation helper: leaves stacks/regs explicitly unfolded. -/
theorem eval_set (d : SState) (dst : Fin R) (v : Bool) :
    StructuredCalls.Eval (mkAtom (.set dst v)) 1 d ⟨Function.update d.regs dst v, d.stacks⟩ :=
  .base (.atom (.set dst v) d)

theorem eval_copy (d : SState) (dst src : Fin R) :
    StructuredCalls.Eval (mkAtom (.copy dst src)) 1 d
      ⟨Function.update d.regs dst (d.regs src), d.stacks⟩ :=
  .base (.atom (.copy dst src) d)

theorem eval_bnot (d : SState) (dst src : Fin R) :
    StructuredCalls.Eval (mkAtom (.bnot dst src)) 1 d
      ⟨Function.update d.regs dst (!(d.regs src)), d.stacks⟩ :=
  .base (.atom (.bnot dst src) d)

theorem eval_band (d : SState) (dst a b : Fin R) :
    StructuredCalls.Eval (mkAtom (.band dst a b)) 1 d
      ⟨Function.update d.regs dst (d.regs a && d.regs b), d.stacks⟩ :=
  .base (.atom (.band dst a b) d)

theorem eval_bor (d : SState) (dst a b : Fin R) :
    StructuredCalls.Eval (mkAtom (.bor dst a b)) 1 d
      ⟨Function.update d.regs dst (d.regs a || d.regs b), d.stacks⟩ :=
  .base (.atom (.bor dst a b) d)

theorem eval_bxor (d : SState) (dst a b : Fin R) :
    StructuredCalls.Eval (mkAtom (.bxor dst a b)) 1 d
      ⟨Function.update d.regs dst (d.regs a ^^ d.regs b), d.stacks⟩ :=
  .base (.atom (.bxor dst a b) d)

theorem eval_push (d : SState) (st : Fin S) (src : Fin R) :
    StructuredCalls.Eval (mkAtom (.push st src)) 1 d
      ⟨d.regs, Function.update d.stacks st (d.regs src :: d.stacks st)⟩ :=
  .base (.atom (.push st src) d)

theorem eval_peek (d : SState) (st : Fin S) (val pres : Fin R) :
    StructuredCalls.Eval (mkAtom (.peek st val pres)) 1 d
      ⟨BitProgram.readRegs d.regs val pres (d.stacks st).head?, d.stacks⟩ :=
  .base (.atom (.peek st val pres) d)

theorem eval_pop (d : SState) (st : Fin S) (val pres : Fin R) :
    StructuredCalls.Eval (mkAtom (.pop st val pres)) 1 d
      ⟨BitProgram.readRegs d.regs val pres (d.stacks st).head?,
        Function.update d.stacks st (d.stacks st).tail⟩ :=
  .base (.atom (.pop st val pres) d)

end LayoutAndSpec

/-! ## Section 2: Pure binary, arithmetic, and sorted-run lemmas -/

section PureMath

@[simp] theorem bitVal_false : bitVal false = 0 := rfl
@[simp] theorem bitVal_true : bitVal true = 1 := rfl
@[simp] theorem bitVal_eq_toNat (b : Bool) : bitVal b = b.toNat := by cases b <;> rfl

theorem toNat_append (xs ys : List Bool) :
    BinaryArithmetic.toNat (xs ++ ys) =
      BinaryArithmetic.toNat xs + 2 ^ xs.length * BinaryArithmetic.toNat ys := by
  induction xs with
  | nil => simp [BinaryArithmetic.toNat]
  | cons a rest ih =>
      simp only [List.cons_append, BinaryArithmetic.toNat, List.length_cons, pow_succ', ih]
      ring

theorem toNat_bits (x : ℕ) : BinaryArithmetic.toNat x.bits = x := by
  induction x using Nat.binaryRec with
  | zero => simp [BinaryArithmetic.toNat, Nat.zero_bits]
  | bit b n ih =>
      by_cases hzero : n = 0 ∧ b = false
      · rcases hzero with ⟨rfl, rfl⟩
        simp [Nat.bit_val, BinaryArithmetic.toNat, Nat.zero_bits]
      · have hn : n = 0 → b = true := by
          intro hn0
          cases hb : b
          · exact False.elim (hzero ⟨hn0, hb⟩)
          · rfl
        rw [Nat.bits_append_bit n b hn, BinaryArithmetic.toNat, bitVal_eq_toNat, ih, Nat.bit_val]
        omega

theorem bits_bit (n : ℕ) (b : Bool) (h : n ≠ 0 ∨ b = true) :
    (2 * n + bitVal b).bits = b :: n.bits := by
  have h' : n = 0 → b = true := fun hn => by
    rcases h with hne | hb
    · exact (hne hn).elim
    · exact hb
  have heq : 2 * n + bitVal b = Nat.bit b n := by simp [Nat.bit_val, bitVal_eq_toNat]
  rw [heq]
  exact Nat.bits_append_bit n b h'

theorem bits_eq_nil_iff (x : ℕ) : x.bits = [] ↔ x = 0 := by
  constructor
  · intro h
    have h' := congrArg BinaryArithmetic.toNat h
    simpa [toNat_bits, BinaryArithmetic.toNat] using h'
  · rintro rfl; exact Nat.zero_bits

theorem toNat_bits_step {x : ℕ} {b : Bool} (h : 0 < x ∨ b = true) :
    (2 * x + bitVal b).bits = b :: x.bits :=
  bits_bit x b (by rcases h with hx | hb; exact Or.inl (by omega); exact Or.inr hb)

theorem bits_length_eq_size (x : ℕ) : x.bits.length = x.size := by
  induction x using Nat.binaryRec with
  | zero => simp [Nat.zero_bits]
  | bit b n ih =>
      by_cases hzero : n = 0 ∧ b = false
      · rcases hzero with ⟨rfl, rfl⟩
        simp [Nat.bit_val, Nat.zero_bits]
      · have hn : n = 0 → b = true := by
          intro hn0
          cases hb : b
          · exact False.elim (hzero ⟨hn0, hb⟩)
          · rfl
        rw [Nat.bits_append_bit n b hn, List.length_cons, ih]
        rcases eq_or_ne n 0 with rfl | hne
        · rw [hn rfl]; simp [Nat.bit_val]
        · rw [Nat.size_bit (by rw [Nat.bit_val]; cases b <;> omega)]

theorem bits_length_le_of_lt {x k : ℕ} (hx : x < 2 ^ k) : x.bits.length ≤ k := by
  rw [bits_length_eq_size, Nat.size_le]
  exact hx

theorem prime_bits_length_le {p : ℕ} (_hp : 2 ≤ p) : p.bits.length ≤ bitLen p + 1 := by
  apply bits_length_le_of_lt
  have hc : p ≤ 2 ^ bitLen p := (Nat.clog_le_iff_le_pow (by decide)).mp le_rfl
  have h2 : 2 ^ bitLen p < 2 ^ (bitLen p + 1) := by
    rw [pow_succ']
    have hpos : 0 < 2 ^ bitLen p := pow_pos (by decide) _
    omega
  exact lt_of_le_of_lt hc h2

theorem lt_prime_bits_length_le {x p : ℕ} (hx : x < p) : x.bits.length ≤ bitLen p + 1 := by
  apply bits_length_le_of_lt
  have hc : p ≤ 2 ^ bitLen p := (Nat.clog_le_iff_le_pow (by decide)).mp le_rfl
  have h2 : 2 ^ bitLen p < 2 ^ (bitLen p + 1) := by
    rw [pow_succ']
    have hpos : 0 < 2 ^ bitLen p := pow_pos (by decide) _
    omega
  exact lt_trans hx (lt_of_le_of_lt hc h2)

theorem bits_getLast_true {x : ℕ} (hx : 0 < x) :
    ∃ init, x.bits = init ++ [true] := by
  induction x using Nat.binaryRec with
  | zero => cases hx
  | bit b n ih =>
      by_cases hn0 : n = 0
      · subst hn0
        have hb : b = true := by
          cases hb' : b
          · simp [Nat.bit_val, hb'] at hx
          · rfl
        subst hb
        refine ⟨[], ?_⟩
        simp [Nat.bit_val]
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn0
        obtain ⟨init, hinit⟩ := ih hpos
        refine ⟨b :: init, ?_⟩
        rw [Nat.bits_append_bit n b (fun h => (hn0 h).elim), hinit, List.cons_append]

/-- Pure leading-false stripper (applied to MSB-first lists). -/
def stripLeadingFalse : List Bool → List Bool
  | false :: rest => stripLeadingFalse rest
  | l => l

theorem stripLeadingFalse_reverse_snoc_true (l : List Bool) :
    stripLeadingFalse ((l ++ [true]).reverse) = (l ++ [true]).reverse := by
  simp [stripLeadingFalse]

theorem bits_snoc_true (l : List Bool) :
    (BinaryArithmetic.toNat (l ++ [true])).bits = l ++ [true] := by
  induction l with
  | nil => simp [BinaryArithmetic.toNat]
  | cons a rest ih =>
      simp only [List.cons_append, BinaryArithmetic.toNat]
      have hpos : 0 < BinaryArithmetic.toNat (rest ++ [true]) := by
        rw [toNat_append]
        have h1 : 1 ≤ 2 ^ rest.length := Nat.one_le_pow _ _ (by decide)
        have htrue : BinaryArithmetic.toNat [true] = 1 := rfl
        rw [htrue]
        nlinarith
      rw [add_comm, toNat_bits_step (Or.inl hpos), ih]

theorem stripLeadingFalse_reverse_eq (l : List Bool) :
    stripLeadingFalse l.reverse = (BinaryArithmetic.toNat l).bits.reverse := by
  induction l using List.reverseRecOn with
  | nil => simp [stripLeadingFalse, BinaryArithmetic.toNat]
  | append_singleton xs a ih =>
      cases a
      · simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          stripLeadingFalse, toNat_append, BinaryArithmetic.toNat]
        exact ih
      · rw [stripLeadingFalse_reverse_snoc_true, bits_snoc_true]

theorem countWord_reverse_strip (x : ℕ) :
    stripLeadingFalse (countWord x).reverse = x.bits.reverse := by
  rw [stripLeadingFalse_reverse_eq]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [countWord, BinaryArithmetic.toNat]
  · simp [countWord, hx, toNat_bits]

theorem countWord_length_le (x : ℕ) : (countWord x).length ≤ max 1 x.bits.length := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [countWord]
  · simp [countWord, hx]

theorem frame_length (w : List Bool) : (Encoding.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => simp [Encoding.frame]
  | cons a rest ih =>
      simp only [Encoding.frame] at ih ⊢
      simp [List.length_cons, ih]
      omega

theorem encodeNatListBin_length (xs : List ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hx : ∀ x ∈ xs, x.bits.length ≤ B) :
    (encodeNatListBin xs).length ≤ (2 * B + 3) * xs.length + 1 := by
  induction xs with
  | nil => simp [encodeNatListBin, Encoding.encodeList]
  | cons a rest ih =>
      have ha : (countWord a).length ≤ B :=
        (countWord_length_le a).trans (max_le hB (hx a (by simp)))
      have hrest := ih (fun y hy => hx y (by simp [hy]))
      simp only [encodeNatListBin, Encoding.encodeList, List.length_cons, List.length_append,
        frame_length] at hrest ⊢
      nlinarith

theorem powBits_eq_pow_mod (p a : ℕ) (bs : List Bool) :
    powBits p a bs = (a ^ BinaryArithmetic.toNat bs) % p := by
  induction bs generalizing a with
  | nil => simp [powBits, BinaryArithmetic.toNat]
  | cons b rest ih =>
      simp only [powBits, BinaryArithmetic.toNat, ih]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, bitVal_false, zero_add]
        rw [Nat.mod_mod, ← Nat.pow_mod, ← sq, ← pow_mul]
      · simp only [↓reduceIte, bitVal_true]
        rw [Nat.mul_mod, ← Nat.pow_mod, ← sq, ← pow_mul, Nat.mod_mod,
          ← Nat.mul_mod, ← pow_succ', show 2 * BinaryArithmetic.toNat rest + 1 =
            1 + 2 * BinaryArithmetic.toNat rest from by omega]

theorem powMod_eq (p a e : ℕ) : powMod p a e = (a ^ e) % p := by
  unfold powMod
  rw [powBits_eq_pow_mod, toNat_bits]

theorem powMod_acc_step (p acc base : ℕ) (b : Bool) (bs : List Bool) :
    (acc * ((if b then base else 1) * (base * base) ^ BinaryArithmetic.toNat bs)) % p =
      (((if b then (acc * base) % p else acc) * ((base * base) % p) ^ BinaryArithmetic.toNat bs)) % p := by
  cases b
  · simp [Nat.mul_mod, Nat.pow_mod]
  · simp only [ite_true]
    calc
      (acc * (base * (base * base) ^ BinaryArithmetic.toNat bs)) % p
          = ((acc * base) * (base * base) ^ BinaryArithmetic.toNat bs) % p := by ring_nf
      _ = (((acc * base) % p) * (((base * base) ^ BinaryArithmetic.toNat bs) % p)) % p := by
            rw [Nat.mul_mod]
      _ = (((acc * base) % p) * (((base * base) % p) ^ BinaryArithmetic.toNat bs)) % p := by
            rw [Nat.pow_mod]
            simp [Nat.mul_mod]

theorem residueProduct_eq_prod_mod (p : ℕ) (xs : List ℕ) :
    residueProduct p xs = xs.prod % p := by
  induction xs with
  | nil => simp [residueProduct]
  | cons a rest ih =>
      simp only [residueProduct, ih, List.prod_cons]
      rw [Nat.mul_mod_mod]

/-- Iterative sorted-run formulation matching our Turing-machine loop. -/
def scanIter (p acc : ℕ) : List ℕ → List ℕ → ℕ
  | [], _ => acc
  | r :: rest, us =>
      let n := p - 1
      let dups := rest.takeWhile (· == r)
      let tail := rest.dropWhile (· == r)
      let rp := r ^ (dups.length + 1)
      let w := firstWitness p (n / r) us
      let v := powMod p w (n / rp)
      scanIter p ((acc * v) % p) tail us
  termination_by fs _ => fs.length
  decreasing_by
    have hle := List.length_dropWhile_le (p := (· == r)) (l := rest)
    simp; omega

theorem sorted_span_props_aux (r : ℕ) (rest : List ℕ)
    (hrel : ∀ x ∈ rest, r ≤ x) (hsort : rest.Pairwise (· ≤ ·)) :
    let dups := rest.takeWhile (· == r)
    let tail := rest.dropWhile (· == r)
    (∀ x ∈ dups, x = r) ∧
    (r ∉ tail) ∧
    tail.Pairwise (· ≤ ·) ∧
    rest = dups ++ tail ∧
    (r :: rest).count r = dups.length + 1 ∧
    ((r :: rest).dedup = r :: tail.dedup) ∧
    (∀ y ∈ tail, (r :: rest).count y = tail.count y) := by
  induction rest with
  | nil => simp
  | cons y ys ih =>
      have hry : r ≤ y := hrel y (by simp)
      have hys_rel : ∀ z ∈ ys, y ≤ z := (List.pairwise_cons.mp hsort).1
      have hys_sort : ys.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsort).2
      by_cases hy : y = r
      · subst hy
        obtain ⟨hd, hn, hts, hsp, hcr, hdd, hco⟩ := ih hys_rel hys_sort
        simp only [List.takeWhile_cons, List.dropWhile_cons, beq_self_eq_true, ↓reduceIte]
        refine ⟨?_, hn, hts, ?_, ?_, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx'
          · exact rfl
          · exact hd x hx'
        · simpa [List.cons_append] using congrArg (y :: ·) hsp
        · rw [List.count_cons_self] at hcr ⊢
          simp [hcr, List.length_cons]
        · have hmem : y ∈ y :: ys := by simp
          rw [List.dedup_cons_of_mem hmem]
          exact hdd
        · intro z hz
          have hzy : z ≠ y := fun h => hn (h ▸ hz)
          have hco' := hco z hz
          simp only [List.count_cons, beq_iff_eq, hzy.symm, if_false, add_zero] at hco' ⊢
          exact hco'
      · have hbeq : (y == r) = false := beq_false_of_ne hy
        have hn : r ∉ y :: ys := by
          intro hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hys'
          · exact hy rfl
          · have := hys_rel r hys'
            omega
        simp only [List.takeWhile_cons, List.dropWhile_cons, hbeq, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by simp, hn, hsort, rfl, ?_, ?_, ?_⟩
        · rw [List.count_cons_self, List.count_eq_zero.mpr hn]
          simp
        · exact List.dedup_cons_of_notMem hn
        · intro z hz
          have hne : z ≠ r := fun h => hn (h ▸ hz)
          simp [List.count_cons, hne.symm]

theorem sorted_span_props {r : ℕ} {rest : List ℕ}
    (hsort : (r :: rest).Pairwise (· ≤ ·)) :
    let dups := rest.takeWhile (· == r)
    let tail := rest.dropWhile (· == r)
    (∀ x ∈ dups, x = r) ∧
    (r ∉ tail) ∧
    tail.Pairwise (· ≤ ·) ∧
    rest = dups ++ tail ∧
    (r :: rest).count r = dups.length + 1 ∧
    ((r :: rest).dedup = r :: tail.dedup) ∧
    (∀ y ∈ tail, (r :: rest).count y = tail.count y) :=
  sorted_span_props_aux r rest (List.pairwise_cons.mp hsort).1 (List.pairwise_cons.mp hsort).2

theorem scanIter_eq_prod_aux (k p acc : ℕ) (fs us : List ℕ)
    (hlen : fs.length ≤ k) (hacc : acc < p) (hsort : fs.Pairwise (· ≤ ·)) :
    scanIter p acc fs us =
      (acc * (fs.dedup.map (fun r => powMod p (firstWitness p ((p - 1) / r) us)
        ((p - 1) / r ^ (fs.count r)))).prod) % p := by
  induction k generalizing acc fs with
  | zero =>
      cases fs with
      | nil => simp [scanIter, Nat.mod_eq_of_lt hacc]
      | cons _ _ => simp at hlen
  | succ k ih =>
      cases fs with
      | nil => simp [scanIter, Nat.mod_eq_of_lt hacc]
      | cons r rest =>
          have hprops := sorted_span_props hsort
          rcases hprops with ⟨_, _, htailSort, _, hcount_r, hdedup, hcount_other⟩
          have hdrop_len : (rest.dropWhile (· == r)).length ≤ k := by
            have := List.length_dropWhile_le (p := (· == r)) (l := rest)
            simp only [List.length_cons] at hlen
            omega
          have hp_pos : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hacc
          have ih' := ih ((acc * powMod p (firstWitness p ((p - 1) / r) us)
              ((p - 1) / r ^ ((rest.takeWhile (· == r)).length + 1))) % p)
            (rest.dropWhile (· == r)) hdrop_len (Nat.mod_lt _ hp_pos) htailSort
          simp only [scanIter]
          rw [ih', hdedup, List.map_cons, List.prod_cons, hcount_r]
          have hmap : List.map (fun x => powMod p (firstWitness p ((p - 1) / x) us)
              ((p - 1) / x ^ (rest.dropWhile (· == r)).count x))
              (rest.dropWhile (· == r)).dedup =
            List.map (fun x => powMod p (firstWitness p ((p - 1) / x) us)
              ((p - 1) / x ^ (r :: rest).count x))
              (rest.dropWhile (· == r)).dedup := by
            apply List.map_congr_left
            intro y hy
            have hy' : y ∈ rest.dropWhile (· == r) := (List.mem_dedup).mp hy
            rw [hcount_other y hy']
          rw [hmap, Nat.mod_mul_mod, mul_assoc]

theorem scanIter_eq_scan {p : ℕ} (hp : 2 ≤ p) (fs us : List ℕ)
    (hsort : fs.Pairwise (· ≤ ·)) :
    scanIter p 1 fs us = scan p fs us := by
  rw [scanIter_eq_prod_aux fs.length p 1 fs us le_rfl (by omega) hsort]
  simp [scan, residueProduct_eq_prod_mod]

theorem primeFactorsList_pairwise (m : ℕ) : m.primeFactorsList.Pairwise (· ≤ ·) := by
  have hs := Nat.primeFactorsList_sorted m
  exact List.pairwise_iff_get.mpr (fun _ _ hij => hs hij.le)

theorem primeFactorsList_props {p : ℕ} [Fact p.Prime] :
    let fs := (p - 1).primeFactorsList
    2 ≤ p ∧
    fs.length ≤ bitLen p ∧
    (∀ r ∈ fs, 2 ≤ r ∧ r < p) ∧
    (∀ r ∈ fs, r ^ (fs.count r) ≤ p - 1 ∧ r ^ (fs.count r) < p) ∧
    (fs.Pairwise (· ≤ ·)) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hne : p - 1 ≠ 0 := by omega
  have hmem : ∀ r ∈ (p - 1).primeFactorsList, 2 ≤ r ∧ r < p := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactorsList hr
    have hrdvd : r ∣ p - 1 := Nat.dvd_of_mem_primeFactorsList hr
    have hrle : r ≤ p - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hrdvd
    exact ⟨hrp.two_le, by omega⟩
  have hprod : (p - 1).primeFactorsList.prod = p - 1 := Nat.prod_primeFactorsList hne
  have hlen : (p - 1).primeFactorsList.length ≤ bitLen p := by
    have h2 : 2 ^ (p - 1).primeFactorsList.length ≤ (p - 1).primeFactorsList.prod := by
      calc
        2 ^ (p - 1).primeFactorsList.length =
            ((p - 1).primeFactorsList.map (fun _ => 2)).prod := by simp
        _ ≤ (p - 1).primeFactorsList.prod := by
            conv_rhs => rw [← List.map_id (p - 1).primeFactorsList]
            exact List.prod_le_prod' (fun r hr => (hmem r hr).1)
    have hp1 : p - 1 < p := by omega
    have hc : p ≤ 2 ^ bitLen p := (Nat.clog_le_iff_le_pow (by decide)).mp le_rfl
    have hlt : 2 ^ (p - 1).primeFactorsList.length < 2 ^ bitLen p := by omega
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt)
  have pow_count_dvd_prod : ∀ (l : List ℕ) (r : ℕ), r ^ (l.count r) ∣ l.prod := by
    intro l r
    induction l with
    | nil => simp
    | cons a as ih =>
        by_cases ha : a = r
        · subst ha
          rw [List.count_cons_self, List.prod_cons, pow_succ']
          exact Nat.mul_dvd_mul_left _ ih
        · rw [List.count_cons, beq_false_of_ne ha]
          simpa [List.prod_cons] using dvd_mul_of_dvd_right ih a
  have hpow : ∀ r ∈ (p - 1).primeFactorsList,
      r ^ ((p - 1).primeFactorsList.count r) ≤ p - 1 ∧
      r ^ ((p - 1).primeFactorsList.count r) < p := by
    intro r hr
    have hdvd : r ^ ((p - 1).primeFactorsList.count r) ∣ p - 1 := by
      simpa [hprod] using pow_count_dvd_prod (p - 1).primeFactorsList r
    have hle : r ^ ((p - 1).primeFactorsList.count r) ≤ p - 1 :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
    exact ⟨hle, by omega⟩
  exact ⟨hp2, hlen, hmem, hpow, primeFactorsList_pairwise (p - 1)⟩

theorem input_length_le {p : ℕ} [Fact p.Prime] (U : List (ZMod p)ˣ) :
    let us := U.map unitRep
    let fs := (p - 1).primeFactorsList
    let input := Encoding.encodeList id [countWord p, encodeNatListBin fs, encodeNatListBin us]
    input.length ≤ 14 * (bitLen p + 1) ^ 2 * (U.length + 1) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hb1 : 1 ≤ bitLen p + 1 := by omega
  have hb2 : 2 ≤ bitLen p + 1 := by
    have hclog : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  have ⟨_, hfs_len, hfs_mem, _, _⟩ := primeFactorsList_props (p := p)
  have hus_len : (U.map unitRep).length = U.length := List.length_map _
  have hcw_p : (countWord p).length ≤ bitLen p + 1 :=
    (countWord_length_le p).trans (max_le hb1 (prime_bits_length_le hp2))
  have hfs_enc : (encodeNatListBin (p - 1).primeFactorsList).length ≤
      (2 * (bitLen p + 1) + 3) * (bitLen p + 1) + 1 := by
    refine (encodeNatListBin_length _ (bitLen p + 1) hb1 (fun r hr =>
      lt_prime_bits_length_le (hfs_mem r hr).2)).trans ?_
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (hfs_len.trans (Nat.le_succ _))) 1
  have hus_enc : (encodeNatListBin (U.map unitRep)).length ≤
      (2 * (bitLen p + 1) + 3) * U.length + 1 := by
    have hp_nz : NeZero p := ⟨hp.ne_zero⟩
    have hmem : ∀ u ∈ U.map unitRep, u.bits.length ≤ bitLen p + 1 := by
      intro u hu
      rcases List.mem_map.mp hu with ⟨u', _, rfl⟩
      exact lt_prime_bits_length_le (ZMod.val_lt (u' : ZMod p))
    simpa [hus_len] using encodeNatListBin_length (U.map unitRep) (bitLen p + 1) hb1 hmem
  set B := bitLen p + 1
  have hlen_eq : (Encoding.encodeList id [countWord p, encodeNatListBin (p - 1).primeFactorsList,
      encodeNatListBin (U.map unitRep)]).length =
      2 * (countWord p).length + 2 * (encodeNatListBin (p - 1).primeFactorsList).length +
        2 * (encodeNatListBin (U.map unitRep)).length + 7 := by
    simp [Encoding.encodeList, frame_length]; omega
  dsimp only
  rw [hlen_eq]
  have hstep1 : 2 * B + 3 ≤ 4 * B := by omega
  have hfs2 : 2 * (encodeNatListBin (p - 1).primeFactorsList).length ≤ 8 * B ^ 2 + 2 := by
    calc
      2 * (encodeNatListBin (p - 1).primeFactorsList).length
          ≤ 2 * ((2 * B + 3) * B + 1) := by omega
      _ ≤ 2 * ((4 * B) * B + 1) := by
          exact Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.mul_le_mul_right B hstep1) 1)
      _ = 8 * B ^ 2 + 2 := by ring
  have hus2 : 2 * (encodeNatListBin (U.map unitRep)).length ≤ 8 * B * U.length + 2 := by
    calc
      2 * (encodeNatListBin (U.map unitRep)).length
          ≤ 2 * ((2 * B + 3) * U.length + 1) := by omega
      _ ≤ 2 * ((4 * B) * U.length + 1) := by
          exact Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.mul_le_mul_right _ hstep1) 1)
      _ = 8 * B * U.length + 2 := by ring
  have hconst : 2 * B + 11 ≤ 6 * B ^ 2 := by
    nlinarith [hb2]
  have hU_term : 8 * B * U.length ≤ 8 * B ^ 2 * U.length := by
    have : 8 * B ≤ 8 * B ^ 2 := by nlinarith [hb2]
    exact Nat.mul_le_mul_right U.length this
  calc
    2 * (countWord p).length + 2 * (encodeNatListBin (p - 1).primeFactorsList).length +
        2 * (encodeNatListBin (U.map unitRep)).length + 7
        ≤ 2 * B + (8 * B ^ 2 + 2) + (8 * B * U.length + 2) + 7 := by omega
    _ = (2 * B + 11) + 8 * B ^ 2 + 8 * B * U.length := by omega
    _ ≤ 6 * B ^ 2 + 8 * B ^ 2 + 8 * B ^ 2 * U.length := by omega
    _ ≤ 14 * B ^ 2 * (U.length + 1) := by nlinarith [hb2]

end PureMath

/-! ## Section 3: Stack and binary arithmetic subroutines -/

section StackAndArith

/-- Two machine states agree on all caller-preserved control registers (`rFound`, `rHasR`, `rHasNext`). -/
def RegPreserved (a b : SState) : Prop :=
  a.regs rFound = b.regs rFound ∧ a.regs rHasR = b.regs rHasR ∧ a.regs rHasNext = b.regs rHasNext

theorem regPreserved_refl (a : SState) : RegPreserved a a := ⟨rfl, rfl, rfl⟩
theorem regPreserved_trans {a b c : SState} (h₁ : RegPreserved a b) (h₂ : RegPreserved b c) :
    RegPreserved a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

theorem readRegs_eq_val {regs : Fin R → Bool} {v p : Fin R} (h : v ≠ p) (top : Option Bool) :
    BitProgram.readRegs regs v p top v = top.getD false :=
  BitProgram.readRegs_value regs v p top h

theorem readRegs_eq_pres {regs : Fin R → Bool} {v p : Fin R} (top : Option Bool) :
    BitProgram.readRegs regs v p top p = top.isSome :=
  BitProgram.readRegs_present regs v p top

theorem readRegs_eq_other {regs : Fin R → Bool} {v p k : Fin R} (hv : k ≠ v) (hp : k ≠ p)
    (top : Option Bool) : BitProgram.readRegs regs v p top k = regs k := by
  simp [BitProgram.readRegs, Function.update, hv, hp]

theorem regPreserved_update {a : SState} {r : Fin R} (v : Bool) (stk : Fin S → List Bool)
    (h1 : r ≠ rFound) (h2 : r ≠ rHasR) (h3 : r ≠ rHasNext) :
    RegPreserved a ⟨Function.update a.regs r v, stk⟩ := by
  simp [RegPreserved, Function.update_of_ne h1.symm, Function.update_of_ne h2.symm,
    Function.update_of_ne h3.symm]

theorem regPreserved_readRegs {a : SState} {v p : Fin R} (top : Option Bool)
    (stk : Fin S → List Bool)
    (hv1 : v ≠ rFound) (hv2 : v ≠ rHasR) (hv3 : v ≠ rHasNext)
    (hp1 : p ≠ rFound) (hp2 : p ≠ rHasR) (hp3 : p ≠ rHasNext) :
    RegPreserved a ⟨BitProgram.readRegs a.regs v p top, stk⟩ := by
  simp [RegPreserved,
    readRegs_eq_other hv1.symm hp1.symm top,
    readRegs_eq_other hv2.symm hp2.symm top,
    readRegs_eq_other hv3.symm hp3.symm top]

theorem stackBits_le_of_pointwise {s : ℕ} (stk : Fin s → List Bool) (f : Fin s → ℕ)
    (h : ∀ k, (stk k).length ≤ f k) : BitProgram.stackBits stk ≤ ∑ k, f k :=
  Finset.sum_le_sum (fun k _ => h k)

theorem stackLength_le_stackBits {s : ℕ} (stk : Fin s → List Bool) (i : Fin s) :
    (stk i).length ≤ BitProgram.stackBits stk :=
  Finset.single_le_sum (f := fun k => (stk k).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem stackBits_pop_push (stk : Fin S → List Bool) (src dst : Fin S) (hne : src ≠ dst)
    (x : Bool) (xs : List Bool) (hs : stk src = x :: xs) :
    BitProgram.stackBits (Function.update (Function.update stk src xs) dst (x :: stk dst)) =
      BitProgram.stackBits stk := by
  let stk1 := Function.update stk src xs
  have h1 := BitProgram.stackBits_update stk src xs
  have h2 := BitProgram.stackBits_update stk1 dst (x :: stk dst)
  have hdst1 : stk1 dst = stk dst := Function.update_of_ne hne.symm _ stk
  dsimp only [stk1] at h2 hdst1
  rw [hdst1] at h2
  simp only [List.length_cons, hs] at h1 h2
  omega

theorem stackBits_pop_drop_push (stk : Fin S → List Bool) (src dst : Fin S) (hne : src ≠ dst)
    (a b : Bool) (xs : List Bool) (hs : stk src = a :: b :: xs) :
    BitProgram.stackBits (Function.update (Function.update stk src xs) dst (b :: stk dst)) + 1 =
      BitProgram.stackBits stk := by
  let stk1 := Function.update stk src xs
  have h1 := BitProgram.stackBits_update stk src xs
  have h2 := BitProgram.stackBits_update stk1 dst (b :: stk dst)
  have hdst1 : stk1 dst = stk dst := Function.update_of_ne hne.symm _ stk
  dsimp only [stk1] at h2 hdst1
  rw [hdst1] at h2
  simp only [List.length_cons, hs] at h1 h2
  omega

theorem toNat_lt_two_pow (l : List Bool) : BinaryArithmetic.toNat l < 2 ^ l.length := by
  induction l with
  | nil => simp [BinaryArithmetic.toNat]
  | cons b rest ih =>
      simp only [BinaryArithmetic.toNat, List.length_cons, pow_succ']
      cases b <;> simp <;> omega

/-- Pure comparison helper: returns `true` if `toNat xs > toNat ys`, `false` if `<`, and `acc` if `=`. -/
def cmpBitsAux : List Bool → List Bool → Bool → Bool
  | [], [], acc => acc
  | a :: as, [], acc => cmpBitsAux as [] (a || acc)
  | [], b :: bs, acc => cmpBitsAux [] bs ((!b) && acc)
  | a :: as, b :: bs, acc => cmpBitsAux as bs ((a && !b) || (!(a ^^ b) && acc))

theorem cmpBitsAux_step_eq (a b acc : Bool) :
    ((a && !b) || (!(a ^^ b) && acc)) =
      if a = b then acc else a := by
  cases a <;> cases b <;> cases acc <;> rfl

theorem cmpBitsAux_correct (xs ys : List Bool) (acc : Bool) :
    cmpBitsAux xs ys acc =
      if BinaryArithmetic.toNat ys < BinaryArithmetic.toNat xs then true
      else if BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys then false
      else acc := by
  induction xs generalizing ys acc with
  | nil =>
      induction ys generalizing acc with
      | nil => simp [cmpBitsAux, BinaryArithmetic.toNat]
      | cons b bs ih =>
          simp only [cmpBitsAux]
          rw [ih]
          cases b <;> simp only [BinaryArithmetic.toNat, bitVal_false, bitVal_true] <;>
            split_ifs <;> simp
  | cons a as iha =>
      cases ys with
      | nil =>
          simp only [cmpBitsAux]
          rw [iha []]
          cases a <;> simp only [BinaryArithmetic.toNat, bitVal_false, bitVal_true] <;>
            split_ifs <;> simp
      | cons b bs =>
          simp only [cmpBitsAux]
          rw [iha bs]
          cases a <;> cases b <;> cases acc <;>
            simp only [BinaryArithmetic.toNat, bitVal_false, bitVal_true] <;>
            split_ifs <;> simp <;> omega

/-- 1. Clear a single stack `s` (`≤ 3 * len + 2` steps). -/
def clearStack (s : Fin S) : SCmd :=
  mkSeq (mkAtom (.peek s rTmp1 rLoop))
    (mkWhile rLoop (mkSeq (mkAtom (.pop s rTmp1 rTmp2)) (mkAtom (.peek s rTmp1 rLoop))))

theorem clearStack_loop_eval (s : Fin S) (xs : List Bool) (a : SState)
    (hs : a.stacks s = xs) (hl : a.regs rLoop = !xs.isEmpty) :
    ∃ n b, StructuredCalls.Eval
      (mkWhile rLoop (mkSeq (mkAtom (.pop s rTmp1 rTmp2)) (mkAtom (.peek s rTmp1 rLoop))))
      n a b ∧ n = 3 * xs.length + 1 ∧
      b.stacks s = [] ∧ (∀ k, k ≠ s → b.stacks k = a.stacks k) ∧ RegPreserved a b := by
  induction xs generalizing a with
  | nil =>
      simp only [List.isEmpty_nil, Bool.not_true] at hl
      refine ⟨1, a, .while_false hl, rfl, hs, fun _ _ => rfl, regPreserved_refl a⟩
  | cons x rest ih =>
      simp only [List.isEmpty_cons, Bool.not_false] at hl
      let a₁ : SState :=
        ⟨BitProgram.readRegs a.regs rTmp1 rTmp2 (some x), Function.update a.stacks s rest⟩
      have hs₁ : StructuredCalls.Eval (mkAtom (.pop s rTmp1 rTmp2)) 1 a a₁ := by
        simpa [a₁, hs] using eval_pop a s rTmp1 rTmp2
      let a₂ : SState := ⟨BitProgram.readRegs a₁.regs rTmp1 rLoop rest.head?, a₁.stacks⟩
      have hs₂ : StructuredCalls.Eval (mkAtom (.peek s rTmp1 rLoop)) 1 a₁ a₂ := by
        simpa [a₂, a₁, Function.update_self] using eval_peek a₁ s rTmp1 rLoop
      have ha2_loop : a₂.regs rLoop = !rest.isEmpty := by
        simp only [a₂, readRegs_eq_pres]
        cases rest <;> rfl
      have hbody : StructuredCalls.Eval
          (mkSeq (mkAtom (.pop s rTmp1 rTmp2)) (mkAtom (.peek s rTmp1 rLoop))) 2 a a₂ :=
        .seq hs₁ hs₂
      obtain ⟨nt, b, htail, hnt, hbs, hoth, hreg⟩ :=
        ih a₂ (by simp [a₂, a₁]) ha2_loop
      refine ⟨2 + nt + 1, b, .while_true hl hbody htail, by simp [List.length_cons]; omega, hbs, ?_, ?_⟩
      · intro k hk
        simpa [a₂, a₁, Function.update_of_ne hk] using hoth k hk
      · exact regPreserved_trans
          (regPreserved_trans
            (regPreserved_readRegs (some x) _ (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide))
            (regPreserved_readRegs rest.head? _ (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide)))
          hreg

theorem clearStack_eval (s : Fin S) (a : SState) :
    ∃ n b, StructuredCalls.Eval (clearStack s) n a b ∧
      n = 3 * (a.stacks s).length + 2 ∧
      b.stacks s = [] ∧ (∀ k, k ≠ s → b.stacks k = a.stacks k) ∧ RegPreserved a b := by
  let a₁ : SState := ⟨BitProgram.readRegs a.regs rTmp1 rLoop (a.stacks s).head?, a.stacks⟩
  have hp : StructuredCalls.Eval (mkAtom (.peek s rTmp1 rLoop)) 1 a a₁ := eval_peek a s rTmp1 rLoop
  have hloop : a₁.regs rLoop = !(a₁.stacks s).isEmpty := by
    simp only [a₁, readRegs_eq_pres]
    cases a.stacks s <;> rfl
  obtain ⟨nt, b, htail, hnt, hbs, hoth, hreg⟩ := clearStack_loop_eval s (a.stacks s) a₁ rfl hloop
  refine ⟨1 + nt, b, .seq hp htail, by omega, hbs, hoth,
    regPreserved_trans (regPreserved_readRegs _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) hreg⟩

/-- 2. Reverse-move `src` onto `dst` (`= 4 * src.length + 2` steps). -/
def revMoveBody (src dst : Fin S) : SCmd :=
  mkSeqList [mkAtom (.pop src rVal rTmp2), mkAtom (.push dst rVal), mkAtom (.peek src rTmp1 rLoop)]

def revMove (src dst : Fin S) : SCmd :=
  mkSeq (mkAtom (.peek src rTmp1 rLoop)) (mkWhile rLoop (revMoveBody src dst))

theorem revMoveBody_eval {src dst : Fin S} (hne : src ≠ dst) {x : Bool} {rest : List Bool}
    (a : SState) (hs : a.stacks src = x :: rest) :
    ∃ b, StructuredCalls.Eval (revMoveBody src dst) 3 a b ∧
      b.stacks src = rest ∧ b.stacks dst = x :: a.stacks dst ∧
      (∀ k, k ≠ src → k ≠ dst → b.stacks k = a.stacks k) ∧
      b.regs rLoop = !rest.isEmpty ∧ RegPreserved a b ∧
      b.regs rEq = a.regs rEq ∧ b.regs rCmp = a.regs rCmp ∧
      BitProgram.stackBits b.stacks = BitProgram.stackBits a.stacks := by
  let a₁ : SState :=
    ⟨BitProgram.readRegs a.regs rVal rTmp2 (some x), Function.update a.stacks src rest⟩
  have h₁ : StructuredCalls.Eval (mkAtom (.pop src rVal rTmp2)) 1 a a₁ := by
    simpa [a₁, hs] using eval_pop a src rVal rTmp2
  let a₂ : SState := ⟨a₁.regs, Function.update a₁.stacks dst (x :: a.stacks dst)⟩
  have h₂ : StructuredCalls.Eval (mkAtom (.push dst rVal)) 1 a₁ a₂ := by
    have hval : a₁.regs rVal = x := by
      dsimp only [a₁]; rw [readRegs_eq_val (by decide : rVal ≠ rTmp2)]; rfl
    have hdst1 : a₁.stacks dst = a.stacks dst := Function.update_of_ne hne.symm _ a.stacks
    have ep := eval_push a₁ dst rVal
    rw [hval, hdst1] at ep
    exact ep
  let a₃ : SState := ⟨BitProgram.readRegs a₂.regs rTmp1 rLoop rest.head?, a₂.stacks⟩
  have h₃ : StructuredCalls.Eval (mkAtom (.peek src rTmp1 rLoop)) 1 a₂ a₃ := by
    have hsrc2 : a₂.stacks src = rest := by simp [a₂, a₁, Function.update_of_ne hne]
    simpa [a₃, hsrc2] using eval_peek a₂ src rTmp1 rLoop
  refine ⟨a₃, .seq h₁ (.seq h₂ h₃), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a₃, a₂, a₁, Function.update_of_ne hne]
  · simp [a₃, a₂]
  · intro k hk1 hk2
    simp [a₃, a₂, a₁, Function.update_of_ne hk1, Function.update_of_ne hk2]
  · simp only [a₃, readRegs_eq_pres]; cases rest <;> rfl
  · exact regPreserved_trans
      (regPreserved_readRegs (some x) _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      (regPreserved_readRegs rest.head? _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
  · dsimp only [a₃, a₂, a₁]
    rw [readRegs_eq_other (by decide) (by decide), readRegs_eq_other (by decide) (by decide)]
  · dsimp only [a₃, a₂, a₁]
    rw [readRegs_eq_other (by decide) (by decide), readRegs_eq_other (by decide) (by decide)]
  · exact stackBits_pop_push a.stacks src dst hne x rest hs

theorem revMove_loop_eval {src dst : Fin S} (hne : src ≠ dst) (xs : List Bool) (a : SState)
    (hs : a.stacks src = xs) (hl : a.regs rLoop = !xs.isEmpty) :
    ∃ n b, StructuredCalls.Eval (mkWhile rLoop (revMoveBody src dst)) n a b ∧
      n = 4 * xs.length + 1 ∧
      b.stacks src = [] ∧ b.stacks dst = xs.reverse ++ a.stacks dst ∧
      (∀ k, k ≠ src → k ≠ dst → b.stacks k = a.stacks k) ∧
      RegPreserved a b ∧ b.regs rEq = a.regs rEq ∧ b.regs rCmp = a.regs rCmp ∧
      BitProgram.stackBits b.stacks = BitProgram.stackBits a.stacks := by
  induction xs generalizing a with
  | nil =>
      simp only [List.isEmpty_nil, Bool.not_true] at hl
      exact ⟨1, a, .while_false hl, rfl, hs, by simp, fun _ _ _ => rfl,
        regPreserved_refl a, rfl, rfl, rfl⟩
  | cons x rest ih =>
      simp only [List.isEmpty_cons, Bool.not_false] at hl
      obtain ⟨m, hb, hm_src, hm_dst, hm_oth, hm_loop, hm_reg, hm_eq, hm_cmp, hm_bits⟩ :=
        revMoveBody_eval hne a hs
      obtain ⟨nt, b, htail, hnt, hbs, hbd, hoth, hreg, heq, hcmp, hbits⟩ := ih m hm_src hm_loop
      refine ⟨3 + nt + 1, b, .while_true hl hb htail, by simp [List.length_cons]; omega,
        hbs, ?_, ?_, ?_, heq.trans hm_eq, hcmp.trans hm_cmp, ?_⟩
      · simp [hbd, hm_dst]
      · intro k hk1 hk2; exact (hoth k hk1 hk2).trans (hm_oth k hk1 hk2)
      · exact regPreserved_trans hm_reg hreg
      · exact hbits.trans hm_bits

theorem revMove_eval {src dst : Fin S} (hne : src ≠ dst) (a : SState) :
    ∃ n b, StructuredCalls.Eval (revMove src dst) n a b ∧
      n = 4 * (a.stacks src).length + 2 ∧
      b.stacks src = [] ∧ b.stacks dst = (a.stacks src).reverse ++ a.stacks dst ∧
      (∀ k, k ≠ src → k ≠ dst → b.stacks k = a.stacks k) ∧
      RegPreserved a b ∧ b.regs rEq = a.regs rEq ∧ b.regs rCmp = a.regs rCmp ∧
      BitProgram.stackBits b.stacks = BitProgram.stackBits a.stacks := by
  let a₁ : SState := ⟨BitProgram.readRegs a.regs rTmp1 rLoop (a.stacks src).head?, a.stacks⟩
  have hp : StructuredCalls.Eval (mkAtom (.peek src rTmp1 rLoop)) 1 a a₁ := eval_peek a src rTmp1 rLoop
  have hloop : a₁.regs rLoop = !(a₁.stacks src).isEmpty := by
    simp only [a₁, readRegs_eq_pres]; cases a.stacks src <;> rfl
  obtain ⟨nt, b, htail, hnt, hbs, hbd, hoth, hreg, heq, hcmp, hbits⟩ :=
    revMove_loop_eval hne (a.stacks src) a₁ rfl hloop
  refine ⟨1 + nt, b, .seq hp htail, by omega, hbs, hbd, hoth,
    regPreserved_trans (regPreserved_readRegs _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) hreg,
    by simpa [a₁, readRegs_eq_other] using heq,
    by simpa [a₁, readRegs_eq_other] using hcmp, hbits⟩

/-- `Spec` wrapper for `revMove`: uniform bound `BitProgram.stackBits a.stacks + 3` (`Spec.while`). -/
theorem revMove_spec {inS outS : Fin S} {src dst : Fin S} (hne : src ≠ dst) (a : SState)
    {B : ℕ} (hB : BitProgram.stackBits a.stacks + 3 ≤ B) :
    ∃ n b, Spec inS outS (revMove src dst) a b n B ∧
      n = 4 * (a.stacks src).length + 2 ∧
      b.stacks src = [] ∧ b.stacks dst = (a.stacks src).reverse ++ a.stacks dst ∧
      (∀ k, k ≠ src → k ≠ dst → b.stacks k = a.stacks k) ∧
      RegPreserved a b ∧
      BitProgram.stackBits b.stacks = BitProgram.stackBits a.stacks := by
  let a₁ : SState := ⟨BitProgram.readRegs a.regs rTmp1 rLoop (a.stacks src).head?, a.stacks⟩
  have hp : Spec inS outS (mkAtom (.peek src rTmp1 rLoop)) a a₁ 1 B :=
    Spec.atom inS outS _ a (by omega)
  have hloop : a₁.regs rLoop = !(a₁.stacks src).isEmpty := by
    simp only [a₁, readRegs_eq_pres]; cases a.stacks src <;> rfl
  obtain ⟨nt, b, htail_ev, hnt, hbs, hbd, hoth, hreg, _, _, hbits⟩ :=
    revMove_loop_eval hne (a.stacks src) a₁ rfl hloop
  let I : SState → Prop := fun x =>
    x.regs rLoop = !(x.stacks src).isEmpty ∧
    BitProgram.stackBits x.stacks ≤ BitProgram.stackBits a.stacks
  have hinit : ∀ x, I x → ∀ i, (x.stacks i).length ≤ B := by
    intro x hx i
    exact (stackLength_le_stackBits x.stacks i).trans (hx.2.trans (by omega))
  have hstep : ∀ x, I x → x.regs rLoop = true →
      ∃ m y, Spec inS outS (revMoveBody src dst) x y m B ∧ I y := by
    intro x hx ht
    cases hxs : x.stacks src with
    | nil =>
        have hfl := hx.1
        rw [hxs] at hfl
        simp at hfl; rw [hfl] at ht; cases ht
    | cons hd tl =>
        obtain ⟨y, hy_ev, hy_src, _, _, hy_loop, _, _, _, hy_bits⟩ := revMoveBody_eval hne x hxs
        exact ⟨3, y, Spec.of_eval_local hy_ev (by omega),
          by rw [hy_src]; exact hy_loop, by rw [hy_bits]; exact hx.2⟩
  have hloop_spec : Spec inS outS (mkWhile rLoop (revMoveBody src dst)) a₁ b nt B :=
    Spec.while inS outS (revMoveBody src dst) rLoop I B hinit hstep htail_ev ⟨hloop, le_rfl⟩
  refine ⟨1 + nt, b, Spec.seq hp hloop_spec, by omega, hbs, hbd, hoth,
    regPreserved_trans (regPreserved_readRegs _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) hreg, hbits⟩

/-- 3. Order-preserving move `src → dst` using scratch `tmp` (`tmp` empty before/after). -/
def moveStack (src dst tmp : Fin S) : SCmd :=
  mkSeqList [clearStack dst, revMove src tmp, revMove tmp dst]

theorem moveStack_eval {src dst tmp : Fin S} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (a : SState) (htmp : a.stacks tmp = []) :
    ∃ n b, StructuredCalls.Eval (moveStack src dst tmp) n a b ∧
      n = 3 * (a.stacks dst).length + 8 * (a.stacks src).length + 6 ∧
      b.stacks src = [] ∧ b.stacks dst = a.stacks src ∧ b.stacks tmp = [] ∧
      (∀ k, k ≠ src → k ≠ dst → k ≠ tmp → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  obtain ⟨n₁, b₁, e₁, hn₁, h1d, h1o, h1r⟩ := clearStack_eval dst a
  have h1s : b₁.stacks src = a.stacks src := h1o src h1
  have h1t : b₁.stacks tmp = [] := (h1o tmp h3.symm).trans htmp
  obtain ⟨n₂, b₂, e₂, hn₂, h2s, h2t, h2o, h2r, _, _, _⟩ := revMove_eval h2 b₁
  have h2d : b₂.stacks dst = [] := (h2o dst h1.symm h3).trans h1d
  obtain ⟨n₃, b₃, e₃, hn₃, h3t, h3d, h3o, h3r, _, _, _⟩ := revMove_eval h3.symm b₂
  have h3s : b₃.stacks src = [] := (h3o src h2 h1).trans h2s
  refine ⟨n₁ + (n₂ + n₃), b₃, .seq e₁ (.seq e₂ e₃), ?_, h3s, ?_, h3t, ?_,
    regPreserved_trans h1r (regPreserved_trans h2r h3r)⟩
  · rw [hn₁, hn₂, hn₃, h2t, h1s, h1t]; simp; omega
  · rw [h3d, h2t, h1t, h2d]; simp [h1s]
  · intro k hks hkd hkt
    rw [h3o k hkt hkd, h2o k hks hkt, h1o k hkd]

/-- 4. Copy `src → dst` via `tmp` (`dst` overwritten, `tmp` empty before/after). -/
def revPushBothBody (src dst1 dst2 : Fin S) : SCmd :=
  mkSeqList [mkAtom (.pop src rVal rTmp2), mkAtom (.push dst1 rVal),
    mkAtom (.push dst2 rVal), mkAtom (.peek src rTmp1 rLoop)]

def revPushBoth (src dst1 dst2 : Fin S) : SCmd :=
  mkSeq (mkAtom (.peek src rTmp1 rLoop)) (mkWhile rLoop (revPushBothBody src dst1 dst2))

theorem revPushBothBody_eval {src dst1 dst2 : Fin S}
    (h1 : src ≠ dst1) (h2 : src ≠ dst2) (h3 : dst1 ≠ dst2)
    {x : Bool} {rest : List Bool} (a : SState) (hs : a.stacks src = x :: rest) :
    ∃ b, StructuredCalls.Eval (revPushBothBody src dst1 dst2) 4 a b ∧
      b.stacks src = rest ∧ b.stacks dst1 = x :: a.stacks dst1 ∧
      b.stacks dst2 = x :: a.stacks dst2 ∧
      (∀ k, k ≠ src → k ≠ dst1 → k ≠ dst2 → b.stacks k = a.stacks k) ∧
      b.regs rLoop = !rest.isEmpty ∧ RegPreserved a b := by
  let a₁ : SState :=
    ⟨BitProgram.readRegs a.regs rVal rTmp2 (some x), Function.update a.stacks src rest⟩
  have e₁ : StructuredCalls.Eval (mkAtom (.pop src rVal rTmp2)) 1 a a₁ := by
    simpa [a₁, hs] using eval_pop a src rVal rTmp2
  have hval : a₁.regs rVal = x := by
    dsimp only [a₁]; rw [readRegs_eq_val (by decide : rVal ≠ rTmp2)]; rfl
  let a₂ : SState := ⟨a₁.regs, Function.update a₁.stacks dst1 (x :: a.stacks dst1)⟩
  have e₂ : StructuredCalls.Eval (mkAtom (.push dst1 rVal)) 1 a₁ a₂ := by
    have hd1 : a₁.stacks dst1 = a.stacks dst1 := Function.update_of_ne h1.symm _ _
    have ep := eval_push a₁ dst1 rVal
    rw [hval, hd1] at ep
    exact ep
  let a₃ : SState := ⟨a₂.regs, Function.update a₂.stacks dst2 (x :: a.stacks dst2)⟩
  have e₃ : StructuredCalls.Eval (mkAtom (.push dst2 rVal)) 1 a₂ a₃ := by
    have hd2 : a₂.stacks dst2 = a.stacks dst2 := by
      simp [a₂, a₁, Function.update_of_ne h3.symm, Function.update_of_ne h2.symm]
    have hv2 : a₂.regs rVal = x := hval
    have ep := eval_push a₂ dst2 rVal
    rw [hv2, hd2] at ep
    exact ep
  let a₄ : SState := ⟨BitProgram.readRegs a₃.regs rTmp1 rLoop rest.head?, a₃.stacks⟩
  have e₄ : StructuredCalls.Eval (mkAtom (.peek src rTmp1 rLoop)) 1 a₃ a₄ := by
    have hs3 : a₃.stacks src = rest := by
      simp [a₃, a₂, a₁, Function.update_of_ne h2, Function.update_of_ne h1]
    simpa [a₄, hs3] using eval_peek a₃ src rTmp1 rLoop
  refine ⟨a₄, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a₄, a₃, a₂, a₁, Function.update_of_ne h2, Function.update_of_ne h1]
  · simp [a₄, a₃, a₂, Function.update_of_ne h3]
  · simp [a₄, a₃]
  · intro k hk0 hk1 hk2
    simp [a₄, a₃, a₂, a₁, Function.update_of_ne hk0, Function.update_of_ne hk1,
      Function.update_of_ne hk2]
  · simp only [a₄, readRegs_eq_pres]; cases rest <;> rfl
  · exact regPreserved_trans
      (regPreserved_readRegs (some x) _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      (regPreserved_readRegs rest.head? _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))

theorem revPushBoth_eval {src dst1 dst2 : Fin S}
    (h1 : src ≠ dst1) (h2 : src ≠ dst2) (h3 : dst1 ≠ dst2) (a : SState) :
    ∃ n b, StructuredCalls.Eval (revPushBoth src dst1 dst2) n a b ∧
      n = 5 * (a.stacks src).length + 2 ∧
      b.stacks src = [] ∧
      b.stacks dst1 = (a.stacks src).reverse ++ a.stacks dst1 ∧
      b.stacks dst2 = (a.stacks src).reverse ++ a.stacks dst2 ∧
      (∀ k, k ≠ src → k ≠ dst1 → k ≠ dst2 → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  have loop_aux : ∀ xs x0, x0.stacks src = xs → x0.regs rLoop = !xs.isEmpty →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop (revPushBothBody src dst1 dst2)) n x0 b ∧
        n = 5 * xs.length + 1 ∧
        b.stacks src = [] ∧
        b.stacks dst1 = xs.reverse ++ x0.stacks dst1 ∧
        b.stacks dst2 = xs.reverse ++ x0.stacks dst2 ∧
        (∀ k, k ≠ src → k ≠ dst1 → k ≠ dst2 → b.stacks k = x0.stacks k) ∧
        RegPreserved x0 b := by
    intro xs
    induction xs with
    | nil =>
        intro x0 hxs hhl
        simp only [List.isEmpty_nil, Bool.not_true] at hhl
        exact ⟨1, x0, .while_false hhl, rfl, hxs, by simp, by simp,
          fun _ _ _ _ => rfl, regPreserved_refl x0⟩
    | cons x rest ih =>
        intro x0 hxs hhl
        simp only [List.isEmpty_cons, Bool.not_false] at hhl
        obtain ⟨m, hb, hms, hmd1, hmd2, hmo, hml, hmr⟩ :=
          revPushBothBody_eval h1 h2 h3 x0 hxs
        obtain ⟨nt, b, ht, hnt, hbs, hbd1, hbd2, hbo, hbr⟩ := ih m hms hml
        refine ⟨4 + nt + 1, b, .while_true hhl hb ht, by simp [List.length_cons]; omega,
          hbs, ?_, ?_, ?_, regPreserved_trans hmr hbr⟩
        · simp [hbd1, hmd1]
        · simp [hbd2, hmd2]
        · intro k hk0 hk1 hk2; exact (hbo k hk0 hk1 hk2).trans (hmo k hk0 hk1 hk2)
  let a₁ : SState := ⟨BitProgram.readRegs a.regs rTmp1 rLoop (a.stacks src).head?, a.stacks⟩
  have hp : StructuredCalls.Eval (mkAtom (.peek src rTmp1 rLoop)) 1 a a₁ := eval_peek a src rTmp1 rLoop
  have hloop : a₁.regs rLoop = !(a₁.stacks src).isEmpty := by
    simp only [a₁, readRegs_eq_pres]; cases a.stacks src <;> rfl
  obtain ⟨nt, b, ht, hnt, hbs, hbd1, hbd2, hbo, hbr⟩ := loop_aux (a.stacks src) a₁ rfl hloop
  refine ⟨1 + nt, b, .seq hp ht, by omega, hbs, hbd1, hbd2, hbo,
    regPreserved_trans (regPreserved_readRegs _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) hbr⟩

def copyStack (src dst tmp : Fin S) : SCmd :=
  mkSeqList [clearStack dst, revMove src tmp, revPushBoth tmp src dst]

theorem copyStack_eval {src dst tmp : Fin S} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (a : SState) (htmp : a.stacks tmp = []) :
    ∃ n b, StructuredCalls.Eval (copyStack src dst tmp) n a b ∧
      n = 3 * (a.stacks dst).length + 9 * (a.stacks src).length + 6 ∧
      b.stacks src = a.stacks src ∧ b.stacks dst = a.stacks src ∧ b.stacks tmp = [] ∧
      (∀ k, k ≠ dst → k ≠ tmp → b.stacks k = a.stacks k) ∧ RegPreserved a b := by
  obtain ⟨n₁, b₁, e₁, hn₁, h1d, h1o, h1r⟩ := clearStack_eval dst a
  have h1s : b₁.stacks src = a.stacks src := h1o src h1
  have h1t : b₁.stacks tmp = [] := (h1o tmp h3.symm).trans htmp
  obtain ⟨n₂, b₂, e₂, hn₂, h2s, h2t, h2o, h2r, _, _, _⟩ := revMove_eval h2 b₁
  have h2d : b₂.stacks dst = [] := (h2o dst h1.symm h3).trans h1d
  obtain ⟨n₃, b₃, e₃, hn₃, h3t, h3s, h3d, h3o, h3r⟩ := revPushBoth_eval h2.symm h3.symm h1 b₂
  refine ⟨n₁ + (n₂ + n₃), b₃, .seq e₁ (.seq e₂ e₃), ?_, ?_, ?_, h3t, ?_,
    regPreserved_trans h1r (regPreserved_trans h2r h3r)⟩
  · rw [hn₁, hn₂, hn₃, h2t, h1s, h1t]; simp; omega
  · rw [h3s, h2s, h2t, h1s, h1t]; simp
  · rw [h3d, h2d, h2t, h1s, h1t]; simp
  · intro k hkd hkt
    by_cases hks : k = src
    · subst hks; rw [h3s, h2s, h2t, h1s, h1t]; simp
    · rw [h3o k hkt hks hkd, h2o k hks hkt, h1o k hkd]

/-- 5. Pop leading `false` bits from `s`, realizing `stripLeadingFalse`. -/
def popLeadingFalseHead (s : Fin S) : SCmd :=
  mkSeqList [mkAtom (.peek s rVal rPres), mkAtom (.bnot rTmp1 rVal),
    mkAtom (.band rLoop rPres rTmp1)]

def popLeadingFalseBody (s : Fin S) : SCmd :=
  mkSeq (mkAtom (.pop s rVal rPres)) (popLeadingFalseHead s)

def popLeadingFalse (s : Fin S) : SCmd :=
  mkSeq (popLeadingFalseHead s) (mkWhile rLoop (popLeadingFalseBody s))

theorem popLeadingFalseHead_eval (s : Fin S) (x : SState) :
    ∃ y, StructuredCalls.Eval (popLeadingFalseHead s) 3 x y ∧
      y.stacks = x.stacks ∧
      y.regs rLoop = (match x.stacks s with | false :: _ => true | _ => false) ∧
      RegPreserved x y := by
  let y₁ : SState := ⟨BitProgram.readRegs x.regs rVal rPres (x.stacks s).head?, x.stacks⟩
  have e₁ := eval_peek x s rVal rPres
  let y₂ : SState := ⟨Function.update y₁.regs rTmp1 (!(y₁.regs rVal)), y₁.stacks⟩
  have e₂ := eval_bnot y₁ rTmp1 rVal
  let y₃ : SState := ⟨Function.update y₂.regs rLoop (y₂.regs rPres && y₂.regs rTmp1), y₂.stacks⟩
  have e₃ := eval_band y₂ rLoop rPres rTmp1
  refine ⟨y₃, .seq e₁ (.seq e₂ e₃), rfl, ?_, ?_⟩
  · simp only [y₃, y₂, y₁, Function.update_self, Function.update_of_ne (by decide : rPres ≠ rTmp1),
      readRegs_eq_pres, readRegs_eq_val (by decide : rVal ≠ rPres)]
    cases hxs : x.stacks s with
    | nil => simp
    | cons b _ => cases b <;> simp
  · exact regPreserved_trans
      (regPreserved_readRegs _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      (regPreserved_trans
        (regPreserved_update _ _ (by decide) (by decide) (by decide))
        (regPreserved_update _ _ (by decide) (by decide) (by decide)))

theorem popLeadingFalse_eval (s : Fin S) (a : SState) :
    ∃ n b, StructuredCalls.Eval (popLeadingFalse s) n a b ∧
      n ≤ 5 * (a.stacks s).length + 4 ∧
      b.stacks s = stripLeadingFalse (a.stacks s) ∧
      (∀ k, k ≠ s → b.stacks k = a.stacks k) ∧ RegPreserved a b := by
  have loop_aux : ∀ xs x0, x0.stacks s = xs →
      x0.regs rLoop = (match xs with | false :: _ => true | _ => false) →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop (popLeadingFalseBody s)) n x0 b ∧
        n ≤ 5 * xs.length + 1 ∧
        b.stacks s = stripLeadingFalse xs ∧
        (∀ k, k ≠ s → b.stacks k = x0.stacks k) ∧ RegPreserved x0 b := by
    intro xs
    induction xs with
    | nil =>
        intro x0 hxs hhl
        simp at hhl
        exact ⟨1, x0, .while_false hhl, by omega, hxs, fun _ _ => rfl, regPreserved_refl x0⟩
    | cons b rest ih =>
        intro x0 hxs hhl
        cases b
        · simp at hhl
          let x₁ : SState :=
            ⟨BitProgram.readRegs x0.regs rVal rPres (some false), Function.update x0.stacks s rest⟩
          have e₁ : StructuredCalls.Eval (mkAtom (.pop s rVal rPres)) 1 x0 x₁ := by
            simpa [x₁, hxs] using eval_pop x0 s rVal rPres
          obtain ⟨x₂, e₂, hx2s, hx2l, hx2r⟩ := popLeadingFalseHead_eval s x₁
          have hxs1 : x₂.stacks s = rest := by rw [hx2s]; simp [x₁]
          obtain ⟨nt, b, ht, hnt, hbs, hbo, hbr⟩ :=
            ih x₂ hxs1 (by simpa [x₁] using hx2l)
          refine ⟨4 + nt + 1, b, .while_true hhl (.seq e₁ e₂) ht, by simp [List.length_cons]; omega,
            hbs, ?_, ?_⟩
          · intro k hk
            have := hbo k hk
            rw [hx2s] at this
            simpa [x₁, Function.update_of_ne hk] using this
          · exact regPreserved_trans
              (regPreserved_readRegs (some false) _ (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide))
              (regPreserved_trans hx2r hbr)
        · simp at hhl
          exact ⟨1, x0, .while_false hhl, Nat.le_add_left 1 _, by simpa [stripLeadingFalse] using hxs,
            fun _ _ => rfl, regPreserved_refl x0⟩
  obtain ⟨a₁, e₁, ha1s, ha1l, ha1r⟩ := popLeadingFalseHead_eval s a
  obtain ⟨nt, b, e₂, hnt, hbs, hbo, hbr⟩ :=
    loop_aux (a.stacks s) a₁ (by rw [ha1s]) ha1l
  refine ⟨3 + nt, b, .seq e₁ e₂, by omega, hbs, ?_, regPreserved_trans ha1r hbr⟩
  · intro k hk; rw [hbo k hk, ha1s]

/-- 6. Normalize stack `s` to canonical `Nat.bits` (`tmp` empty before/after). -/
def stripZeros (s tmp : Fin S) : SCmd :=
  mkSeqList [revMove s tmp, popLeadingFalse tmp, revMove tmp s]

theorem stripZeros_eval {s tmp : Fin S} (hne : s ≠ tmp) (a : SState) (htmp : a.stacks tmp = []) :
    ∃ n b, StructuredCalls.Eval (stripZeros s tmp) n a b ∧
      n ≤ 13 * (a.stacks s).length + 8 ∧
      b.stacks s = (BinaryArithmetic.toNat (a.stacks s)).bits ∧
      b.stacks tmp = [] ∧
      (∀ k, k ≠ s → k ≠ tmp → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  obtain ⟨n₁, b₁, e₁, hn₁, h1s, h1t, h1o, h1r, _, _, _⟩ := revMove_eval hne a
  rw [htmp, List.append_nil] at h1t
  obtain ⟨n₂, b₂, e₂, hn₂, h2t, h2o, h2r⟩ := popLeadingFalse_eval tmp b₁
  have h2s : b₂.stacks s = [] := (h2o s hne).trans h1s
  obtain ⟨n₃, b₃, e₃, hn₃, h3t, h3s, h3o, h3r, _, _, _⟩ := revMove_eval hne.symm b₂
  refine ⟨n₁ + (n₂ + n₃), b₃, .seq e₁ (.seq e₂ e₃), ?_, ?_, h3t, ?_,
    regPreserved_trans h1r (regPreserved_trans h2r h3r)⟩
  · rw [h1t, List.length_reverse] at hn₂
    rw [hn₁, hn₃, h2t, h1t]
    have : (stripLeadingFalse (a.stacks s).reverse).length ≤ (a.stacks s).length := by
      rw [stripLeadingFalse_reverse_eq, List.length_reverse]
      exact bits_length_le_of_lt (toNat_lt_two_pow (a.stacks s))
    omega
  · rw [h3s, h2s, List.append_nil, h2t, h1t, stripLeadingFalse_reverse_eq, List.reverse_reverse]
  · intro k hks hkt
    rw [h3o k hkt hks, h2o k hkt, h1o k hks hkt]

/-- 7. Check whether stack `s` equals `[true]` (`rEq`), preserving all stacks (`≤ 7` steps). -/
def isOne (s : Fin S) : SCmd :=
  mkSeq (mkAtom (.pop s rVal rPres))
    (mkIte rPres
      (mkSeqList [mkAtom (.peek s rVal2 rPres2), mkAtom (.bnot rTmp1 rPres2),
        mkAtom (.band rEq rVal rTmp1), mkAtom (.push s rVal)])
      (mkAtom (.set rEq false)))

theorem isOne_eval (s : Fin S) (a : SState) :
    ∃ n b, StructuredCalls.Eval (isOne s) n a b ∧ n ≤ 7 ∧
      b.stacks = a.stacks ∧ b.regs rEq = decide (a.stacks s = [true]) ∧ RegPreserved a b := by
  cases hs : a.stacks s with
  | nil =>
      let a₁ : SState := ⟨BitProgram.readRegs a.regs rVal rPres none, Function.update a.stacks s []⟩
      have e₁ : StructuredCalls.Eval (mkAtom (.pop s rVal rPres)) 1 a a₁ := by
        simpa [a₁, hs] using eval_pop a s rVal rPres
      have hp : a₁.regs rPres = false := by simp [a₁, readRegs_eq_pres]
      let a₂ : SState := ⟨Function.update a₁.regs rEq false, a₁.stacks⟩
      have e₂ := eval_set a₁ rEq false
      refine ⟨1 + (1 + 1), a₂, .seq e₁ (.ite_false hp e₂), by omega, ?_, by simp [a₂], ?_⟩
      · funext k
        by_cases hk : k = s
        · subst hk; simp [a₂, a₁, hs]
        · simp [a₂, a₁, Function.update_of_ne hk]
      · exact regPreserved_trans
          (regPreserved_readRegs none _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide))
          (regPreserved_update _ _ (by decide) (by decide) (by decide))
  | cons v rest =>
      let a₁ : SState := ⟨BitProgram.readRegs a.regs rVal rPres (some v), Function.update a.stacks s rest⟩
      have e₁ : StructuredCalls.Eval (mkAtom (.pop s rVal rPres)) 1 a a₁ := by
        simpa [a₁, hs] using eval_pop a s rVal rPres
      have hp : a₁.regs rPres = true := by simp [a₁, readRegs_eq_pres]
      have hv : a₁.regs rVal = v := by
        dsimp only [a₁]; rw [readRegs_eq_val (by decide : rVal ≠ rPres)]; rfl
      let a₂ : SState := ⟨BitProgram.readRegs a₁.regs rVal2 rPres2 rest.head?, a₁.stacks⟩
      have e₂ : StructuredCalls.Eval (mkAtom (.peek s rVal2 rPres2)) 1 a₁ a₂ := by
        simpa [a₂, a₁] using eval_peek a₁ s rVal2 rPres2
      let a₃ : SState := ⟨Function.update a₂.regs rTmp1 (!(a₂.regs rPres2)), a₂.stacks⟩
      have e₃ := eval_bnot a₂ rTmp1 rPres2
      let a₄ : SState := ⟨Function.update a₃.regs rEq (a₃.regs rVal && a₃.regs rTmp1), a₃.stacks⟩
      have e₄ := eval_band a₃ rEq rVal rTmp1
      let a₅ : SState := ⟨a₄.regs, Function.update a₄.stacks s (a₄.regs rVal :: a₄.stacks s)⟩
      have e₅ := eval_push a₄ s rVal
      have hv4 : a₄.regs rVal = v := by
        simp only [a₄, a₃, a₂, a₁, BitProgram.readRegs, Function.update, Fin.ext_iff]
        norm_num
      refine ⟨1 + (4 + 1), a₅, .seq e₁ (.ite_true hp (.seq e₂ (.seq e₃ (.seq e₄ e₅)))),
        by omega, ?_, ?_, ?_⟩
      · funext k
        by_cases hk : k = s
        · subst hk; dsimp only [a₅]; rw [Function.update_self, hv4]; simp [a₄, a₃, a₂, a₁, hs]
        · simp [a₅, a₄, a₃, a₂, a₁, Function.update_of_ne hk]
      · simp only [a₅, a₄, a₃, a₂, a₁, BitProgram.readRegs, Function.update, Fin.ext_iff]
        norm_num
        cases v <;> cases rest <;> rfl
      · exact regPreserved_trans
          (regPreserved_readRegs (some v) _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide))
          (regPreserved_trans
            (regPreserved_readRegs rest.head? _ (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide))
            (regPreserved_trans
              (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_update _ _ (by decide) (by decide) (by decide))))

/-- 8. Non-destructive equality test `s1 == s2` into `rEq` (`tmp1, tmp2` empty before/after). -/
def peekOrCond (s1 s2 : Fin S) : SCmd :=
  mkSeqList [mkAtom (.peek s1 rTmp1 rPres), mkAtom (.peek s2 rTmp2 rPres2),
    mkAtom (.bor rLoop rPres rPres2)]

theorem peekOrCond_eval (s1 s2 : Fin S) (x : SState) :
    ∃ y, StructuredCalls.Eval (peekOrCond s1 s2) 3 x y ∧
      y.stacks = x.stacks ∧
      y.regs rLoop = (!(x.stacks s1).isEmpty || !(x.stacks s2).isEmpty) ∧
      y.regs rEq = x.regs rEq ∧ y.regs rCmp = x.regs rCmp ∧
      y.regs rCarry = x.regs rCarry ∧ RegPreserved x y := by
  let y₁ : SState := ⟨BitProgram.readRegs x.regs rTmp1 rPres (x.stacks s1).head?, x.stacks⟩
  have e₁ := eval_peek x s1 rTmp1 rPres
  let y₂ : SState := ⟨BitProgram.readRegs y₁.regs rTmp2 rPres2 (x.stacks s2).head?, x.stacks⟩
  have e₂ : StructuredCalls.Eval (mkAtom (.peek s2 rTmp2 rPres2)) 1 y₁ y₂ := eval_peek y₁ s2 rTmp2 rPres2
  let y₃ : SState := ⟨Function.update y₂.regs rLoop (y₂.regs rPres || y₂.regs rPres2), y₂.stacks⟩
  have e₃ := eval_bor y₂ rLoop rPres rPres2
  refine ⟨y₃, .seq e₁ (.seq e₂ e₃), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [y₃, y₂, y₁, BitProgram.readRegs, Function.update, Fin.ext_iff]
    norm_num
    cases x.stacks s1 <;> cases x.stacks s2 <;> rfl
  · simp only [y₃, y₂, y₁, BitProgram.readRegs, Function.update, Fin.ext_iff]
    norm_num
  · simp only [y₃, y₂, y₁, BitProgram.readRegs, Function.update, Fin.ext_iff]
    norm_num
  · simp only [y₃, y₂, y₁, BitProgram.readRegs, Function.update, Fin.ext_iff]
    norm_num
  · exact regPreserved_trans
      (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (regPreserved_trans
        (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (regPreserved_update _ _ (by decide) (by decide) (by decide)))

/-- Pop `s1, s2`, pushing popped bits onto `tmp1, tmp2` when present. Sets `(rVal, rPres, rVal2, rPres2)`. -/
def popBothBackup (s1 s2 tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.pop s1 rVal rPres),
    mkIte rPres (mkAtom (.push tmp1 rVal)) mkSkip,
    mkAtom (.pop s2 rVal2 rPres2),
    mkIte rPres2 (mkAtom (.push tmp2 rVal2)) mkSkip
  ]

theorem popBothBackup_eval {s1 s2 tmp1 tmp2 : Fin S}
    (h12 : s1 ≠ s2) (h1t1 : s1 ≠ tmp1) (h1t2 : s1 ≠ tmp2)
    (h2t1 : s2 ≠ tmp1) (h2t2 : s2 ≠ tmp2) (ht12 : tmp1 ≠ tmp2)
    (a : SState) :
    ∃ n b, StructuredCalls.Eval (popBothBackup s1 s2 tmp1 tmp2) n a b ∧ n ≤ 6 ∧
      b.stacks s1 = (a.stacks s1).tail ∧ b.stacks s2 = (a.stacks s2).tail ∧
      b.stacks tmp1 = (match a.stacks s1 with | [] => a.stacks tmp1 | x :: _ => x :: a.stacks tmp1) ∧
      b.stacks tmp2 = (match a.stacks s2 with | [] => a.stacks tmp2 | y :: _ => y :: a.stacks tmp2) ∧
      (∀ k, k ≠ s1 → k ≠ s2 → k ≠ tmp1 → k ≠ tmp2 → b.stacks k = a.stacks k) ∧
      b.regs rVal = (a.stacks s1).head?.getD false ∧ b.regs rPres = !(a.stacks s1).isEmpty ∧
      b.regs rVal2 = (a.stacks s2).head?.getD false ∧ b.regs rPres2 = !(a.stacks s2).isEmpty ∧
      b.regs rEq = a.regs rEq ∧ b.regs rCmp = a.regs rCmp ∧ b.regs rCarry = a.regs rCarry ∧
      RegPreserved a b := by
  let a₁ : SState := ⟨BitProgram.readRegs a.regs rVal rPres (a.stacks s1).head?,
    Function.update a.stacks s1 (a.stacks s1).tail⟩
  have e₁ := eval_pop a s1 rVal rPres
  have hpart1 : ∃ n₁ b₁, StructuredCalls.Eval
      (mkIte rPres (mkAtom (.push tmp1 rVal)) mkSkip) n₁ a₁ b₁ ∧ n₁ ≤ 2 ∧
      b₁.regs = a₁.regs ∧ b₁.stacks s1 = (a.stacks s1).tail ∧ b₁.stacks s2 = a.stacks s2 ∧
      b₁.stacks tmp1 = (match a.stacks s1 with | [] => a.stacks tmp1 | x :: _ => x :: a.stacks tmp1) ∧
      b₁.stacks tmp2 = a.stacks tmp2 ∧
      (∀ k, k ≠ s1 → k ≠ tmp1 → b₁.stacks k = a.stacks k) := by
    cases hs1 : a.stacks s1 with
    | nil =>
        have hp : a₁.regs rPres = false := by simp [a₁, hs1, readRegs_eq_pres]
        refine ⟨1, a₁, .ite_false hp (.base (.skip a₁)), by omega, rfl,
          by simp [a₁, hs1], by simp [a₁, Function.update_of_ne h12.symm],
          by simp [a₁, Function.update_of_ne h1t1.symm],
          by simp [a₁, Function.update_of_ne h1t2.symm],
          fun k hk1 _ => by simp [a₁, Function.update_of_ne hk1]⟩
    | cons x rest =>
        have hp : a₁.regs rPres = true := by simp [a₁, hs1, readRegs_eq_pres]
        have hv : a₁.regs rVal = x := by
          dsimp only [a₁]; rw [hs1, readRegs_eq_val (by decide : rVal ≠ rPres)]; rfl
        let b₁ : SState := ⟨a₁.regs, Function.update a₁.stacks tmp1 (x :: a.stacks tmp1)⟩
        have eb₁ : StructuredCalls.Eval (mkAtom (.push tmp1 rVal)) 1 a₁ b₁ := by
          have htm : a₁.stacks tmp1 = a.stacks tmp1 := by simp [a₁, Function.update_of_ne h1t1.symm]
          have ep := eval_push a₁ tmp1 rVal
          rw [hv, htm] at ep
          exact ep
        refine ⟨2, b₁, .ite_true hp eb₁, by omega, rfl,
          by simp [b₁, a₁, Function.update_of_ne h1t1, hs1],
          by simp [b₁, a₁, Function.update_of_ne h2t1, Function.update_of_ne h12.symm],
          by simp [b₁],
          by simp [b₁, a₁, Function.update_of_ne h2t2, Function.update_of_ne ht12.symm, Function.update_of_ne h1t2.symm],
          fun k hk1 hkt1 => by simp [b₁, a₁, Function.update_of_ne hkt1, Function.update_of_ne hk1]⟩
  obtain ⟨n₁, b₁, eb₁, hn₁, hb1r, hb1s1, hb1s2, hb1t1, hb1t2, hb1o⟩ := hpart1
  let a₂ : SState := ⟨BitProgram.readRegs b₁.regs rVal2 rPres2 (a.stacks s2).head?,
    Function.update b₁.stacks s2 (a.stacks s2).tail⟩
  have e₂ : StructuredCalls.Eval (mkAtom (.pop s2 rVal2 rPres2)) 1 b₁ a₂ := by
    simpa [a₂, hb1s2] using eval_pop b₁ s2 rVal2 rPres2
  have hpart2 : ∃ n₂ b₂, StructuredCalls.Eval
      (mkIte rPres2 (mkAtom (.push tmp2 rVal2)) mkSkip) n₂ a₂ b₂ ∧ n₂ ≤ 2 ∧
      b₂.regs = a₂.regs ∧ b₂.stacks s1 = (a.stacks s1).tail ∧ b₂.stacks s2 = (a.stacks s2).tail ∧
      b₂.stacks tmp1 = b₁.stacks tmp1 ∧
      b₂.stacks tmp2 = (match a.stacks s2 with | [] => a.stacks tmp2 | y :: _ => y :: a.stacks tmp2) ∧
      (∀ k, k ≠ s1 → k ≠ s2 → k ≠ tmp1 → k ≠ tmp2 → b₂.stacks k = a.stacks k) := by
    cases hs2 : a.stacks s2 with
    | nil =>
        have hp : a₂.regs rPres2 = false := by simp [a₂, hs2, readRegs_eq_pres]
        refine ⟨1, a₂, .ite_false hp (.base (.skip a₂)), by omega, rfl,
          by simp [a₂, Function.update_of_ne h12, hb1s1],
          by simp [a₂, hs2],
          by simp [a₂, Function.update_of_ne h2t1.symm],
          by simp [a₂, Function.update_of_ne h2t2.symm, hb1t2],
          fun k hk1 hk2 hkt1 _ => by simp [a₂, Function.update_of_ne hk2, hb1o k hk1 hkt1]⟩
    | cons y rest =>
        have hp : a₂.regs rPres2 = true := by simp [a₂, hs2, readRegs_eq_pres]
        have hv : a₂.regs rVal2 = y := by
          dsimp only [a₂]; rw [hs2, readRegs_eq_val (by decide : rVal2 ≠ rPres2)]; rfl
        let b₂ : SState := ⟨a₂.regs, Function.update a₂.stacks tmp2 (y :: a.stacks tmp2)⟩
        have eb₂ : StructuredCalls.Eval (mkAtom (.push tmp2 rVal2)) 1 a₂ b₂ := by
          have htm : a₂.stacks tmp2 = a.stacks tmp2 := by
            simp [a₂, Function.update_of_ne h2t2.symm, hb1t2]
          have ep := eval_push a₂ tmp2 rVal2
          rw [hv, htm] at ep
          exact ep
        refine ⟨2, b₂, .ite_true hp eb₂, by omega, rfl,
          by simp [b₂, a₂, Function.update_of_ne h1t2, Function.update_of_ne h12, hb1s1],
          by simp [b₂, a₂, Function.update_of_ne h2t2, hs2],
          by simp [b₂, a₂, Function.update_of_ne ht12, Function.update_of_ne h2t1.symm],
          by simp [b₂],
          fun k hk1 hk2 hkt1 hkt2 => by
            simp [b₂, a₂, Function.update_of_ne hkt2, Function.update_of_ne hk2, hb1o k hk1 hkt1]⟩
  obtain ⟨n₂, b₂, eb₂, hn₂, hb2r, hb2s1, hb2s2, hb2t1, hb2t2, hb2o⟩ := hpart2
  have hb2_regs : b₂.regs = BitProgram.readRegs
      (BitProgram.readRegs a.regs rVal rPres (a.stacks s1).head?) rVal2 rPres2 (a.stacks s2).head? := by
    rw [hb2r]; simp [a₂, hb1r, a₁]
  refine ⟨1 + (n₁ + (1 + n₂)), b₂, .seq e₁ (.seq eb₁ (.seq e₂ eb₂)), by omega,
    hb2s1, hb2s2, hb2t1.trans hb1t1, hb2t2, hb2o, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb2_regs, readRegs_eq_other (by decide : rVal ≠ rVal2) (by decide : rVal ≠ rPres2),
      readRegs_eq_val (by decide : rVal ≠ rPres)]
  · rw [hb2_regs, readRegs_eq_other (by decide : rPres ≠ rVal2) (by decide : rPres ≠ rPres2),
      readRegs_eq_pres]
    cases a.stacks s1 <;> rfl
  · rw [hb2_regs, readRegs_eq_val (by decide : rVal2 ≠ rPres2)]
  · rw [hb2_regs, readRegs_eq_pres]
    cases a.stacks s2 <;> rfl
  · rw [hb2_regs, readRegs_eq_other (by decide : rEq ≠ rVal2) (by decide : rEq ≠ rPres2),
      readRegs_eq_other (by decide : rEq ≠ rVal) (by decide : rEq ≠ rPres)]
  · rw [hb2_regs, readRegs_eq_other (by decide : rCmp ≠ rVal2) (by decide : rCmp ≠ rPres2),
      readRegs_eq_other (by decide : rCmp ≠ rVal) (by decide : rCmp ≠ rPres)]
  · rw [hb2_regs, readRegs_eq_other (by decide : rCarry ≠ rVal2) (by decide : rCarry ≠ rPres2),
      readRegs_eq_other (by decide : rCarry ≠ rVal) (by decide : rCarry ≠ rPres)]
  · rw [show b₂ = ⟨b₂.regs, b₂.stacks⟩ from rfl, hb2_regs]
    exact regPreserved_trans
      (regPreserved_readRegs (a := a) _ a.stacks (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      (regPreserved_readRegs (a := ⟨BitProgram.readRegs a.regs rVal rPres (a.stacks s1).head?, a.stacks⟩)
        _ b₂.stacks (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

def eqStackBody (s1 s2 tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    popBothBackup s1 s2 tmp1 tmp2,
    mkAtom (.bxor rTmp1 rPres rPres2),
    mkAtom (.bxor rTmp2 rVal rVal2),
    mkAtom (.bor rTmp3 rTmp1 rTmp2),
    mkAtom (.bnot rTmp3 rTmp3),
    mkAtom (.band rEq rEq rTmp3),
    peekOrCond s1 s2
  ]

def eqStack (s1 s2 tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.set rEq true),
    peekOrCond s1 s2,
    mkWhile rLoop (eqStackBody s1 s2 tmp1 tmp2),
    revMove tmp1 s1,
    revMove tmp2 s2
  ]

theorem eqStack_eval {s1 s2 tmp1 tmp2 : Fin S}
    (h12 : s1 ≠ s2) (h1t1 : s1 ≠ tmp1) (h1t2 : s1 ≠ tmp2)
    (h2t1 : s2 ≠ tmp1) (h2t2 : s2 ≠ tmp2) (ht12 : tmp1 ≠ tmp2)
    (a : SState) (ht1 : a.stacks tmp1 = []) (ht2 : a.stacks tmp2 = []) :
    ∃ n b, StructuredCalls.Eval (eqStack s1 s2 tmp1 tmp2) n a b ∧
      n ≤ 26 * ((a.stacks s1).length + (a.stacks s2).length) + 12 ∧
      b.stacks = a.stacks ∧ b.regs rEq = decide (a.stacks s1 = a.stacks s2) ∧ RegPreserved a b := by
  have loop_aux : ∀ m xs ys x0,
      x0.stacks s1 = xs → x0.stacks s2 = ys → xs.length + ys.length ≤ m →
      x0.regs rLoop = (!xs.isEmpty || !ys.isEmpty) →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop (eqStackBody s1 s2 tmp1 tmp2)) n x0 b ∧
        n ≤ 15 * (xs.length + ys.length) + 1 ∧
        b.stacks s1 = [] ∧ b.stacks s2 = [] ∧
        b.stacks tmp1 = xs.reverse ++ x0.stacks tmp1 ∧
        b.stacks tmp2 = ys.reverse ++ x0.stacks tmp2 ∧
        (∀ k, k ≠ s1 → k ≠ s2 → k ≠ tmp1 → k ≠ tmp2 → b.stacks k = x0.stacks k) ∧
        b.regs rEq = (x0.regs rEq && decide (xs = ys)) ∧ RegPreserved x0 b := by
    intro m
    induction m with
    | zero =>
        intro xs ys x0 hxs hys hm hhl
        have hnil1 : xs = [] := List.length_eq_zero_iff.mp (by omega)
        have hnil2 : ys = [] := List.length_eq_zero_iff.mp (by omega)
        subst hnil1; subst hnil2
        simp at hhl
        exact ⟨1, x0, .while_false hhl, by omega, hxs, hys, by simp, by simp,
          fun _ _ _ _ _ => rfl, by simp, regPreserved_refl x0⟩
    | succ m ih =>
        intro xs ys x0 hxs hys hm hhl
        by_cases hdone : xs = [] ∧ ys = []
        · rcases hdone with ⟨rfl, rfl⟩
          simp at hhl
          exact ⟨1, x0, .while_false hhl, by omega, hxs, hys, by simp, by simp,
            fun _ _ _ _ _ => rfl, by simp, regPreserved_refl x0⟩
        · have hloop_t : x0.regs rLoop = true := by
            rw [hhl]
            cases xs with
            | nil =>
                cases ys with
                | nil => exact False.elim (hdone ⟨rfl, rfl⟩)
                | cons _ _ => rfl
            | cons _ _ => rfl
          obtain ⟨nb, b₁, eb₁, hnb₁, hbs1, hbs2, hbt1, hbt2, hbo, hv1, hp1, hv2, hp2,
            heq1, _, _, hreg1⟩ := popBothBackup_eval h12 h1t1 h1t2 h2t1 h2t2 ht12 x0
          let b₂ : SState := ⟨Function.update b₁.regs rTmp1 (b₁.regs rPres ^^ b₁.regs rPres2), b₁.stacks⟩
          have e₂ := eval_bxor b₁ rTmp1 rPres rPres2
          let b₃ : SState := ⟨Function.update b₂.regs rTmp2 (b₂.regs rVal ^^ b₂.regs rVal2), b₂.stacks⟩
          have e₃ := eval_bxor b₂ rTmp2 rVal rVal2
          let b₄ : SState := ⟨Function.update b₃.regs rTmp3 (b₃.regs rTmp1 || b₃.regs rTmp2), b₃.stacks⟩
          have e₄ := eval_bor b₃ rTmp3 rTmp1 rTmp2
          let b₅ : SState := ⟨Function.update b₄.regs rTmp3 (!(b₄.regs rTmp3)), b₄.stacks⟩
          have e₅ := eval_bnot b₄ rTmp3 rTmp3
          let b₆ : SState := ⟨Function.update b₅.regs rEq (b₅.regs rEq && b₅.regs rTmp3), b₅.stacks⟩
          have e₆ := eval_band b₅ rEq rEq rTmp3
          obtain ⟨b₇, e₇, hb7s, hb7l, hb7eq, _, _, hreg7⟩ := peekOrCond_eval s1 s2 b₆
          have hstep_len : xs.tail.length + ys.tail.length ≤ m := by
            cases xs <;> cases ys <;> simp at hm hdone ⊢ <;> omega
          have hbody : StructuredCalls.Eval (eqStackBody s1 s2 tmp1 tmp2) (nb + 8) x0 b₇ := by
            have := StructuredCalls.Eval.seq eb₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
            simpa [eqStackBody, mkSeqList, mkSeq, Nat.add_assoc] using this
          have hb7_s1 : b₇.stacks s1 = xs.tail := by rw [hb7s, hbs1, hxs]
          have hb7_s2 : b₇.stacks s2 = ys.tail := by rw [hb7s, hbs2, hys]
          obtain ⟨nt, fin, htail, hnt, hfs1, hfs2, hft1, hft2, hfo, hfeq, hreg_tail⟩ :=
            ih xs.tail ys.tail b₇ hb7_s1 hb7_s2 hstep_len
              (by rw [← hb7s, hb7_s1, hb7_s2] at hb7l; exact hb7l)
          have hbit_eq : b₇.regs rEq = (x0.regs rEq &&
              (!(b₁.regs rPres ^^ b₁.regs rPres2 || b₁.regs rVal ^^ b₁.regs rVal2))) := by
            simp only [hb7eq, b₆, b₅, b₄, b₃, b₂, heq1, Function.update, Fin.ext_iff]
            norm_num
          have hstep_dec : ((!(b₁.regs rPres ^^ b₁.regs rPres2 || b₁.regs rVal ^^ b₁.regs rVal2)) &&
              decide (xs.tail = ys.tail)) = decide (xs = ys) := by
            rw [hp1, hp2, hv1, hv2, hxs, hys]
            cases xs with
            | nil => cases ys with
              | nil => simp
              | cons _ _ => simp
            | cons a as => cases ys with
              | nil => simp
              | cons b bs =>
                  cases a <;> cases b <;> by_cases has : as = bs <;> simp [has]
          refine ⟨nb + 8 + nt + 1, fin, .while_true hloop_t hbody htail, ?_, hfs1, hfs2, ?_, ?_, ?_, ?_, ?_⟩
          · have hdrop_le : xs.tail.length + ys.tail.length + 1 ≤ xs.length + ys.length := by
              cases xs <;> cases ys <;> simp at hdone ⊢ <;> omega
            omega
          · rw [hft1, hb7s, hbt1, hxs]; cases xs <;> simp
          · rw [hft2, hb7s, hbt2, hys]; cases ys <;> simp
          · intro k hk1 hk2 hkt1 hkt2
            rw [hfo k hk1 hk2 hkt1 hkt2, hb7s, hbo k hk1 hk2 hkt1 hkt2]
          · rw [hfeq, hbit_eq, Bool.and_assoc, hstep_dec]
          · exact regPreserved_trans hreg1
              (regPreserved_trans
                (regPreserved_update _ _ (by decide) (by decide) (by decide))
                (regPreserved_trans
                  (regPreserved_update _ _ (by decide) (by decide) (by decide))
                  (regPreserved_trans
                    (regPreserved_update _ _ (by decide) (by decide) (by decide))
                    (regPreserved_trans
                      (regPreserved_update _ _ (by decide) (by decide) (by decide))
                      (regPreserved_trans
                        (regPreserved_update _ _ (by decide) (by decide) (by decide))
                        (regPreserved_trans hreg7 hreg_tail))))))
  let a₁ : SState := ⟨Function.update a.regs rEq true, a.stacks⟩
  have e₁ := eval_set a rEq true
  obtain ⟨a₂, e₂, ha2s, ha2l, ha2eq, _, _, hreg2⟩ := peekOrCond_eval s1 s2 a₁
  have ha2_eq : a₂.regs rEq = true := by rw [ha2eq]; simp [a₁]
  obtain ⟨n₃, b₃, e₃, hn₃, h3s1, h3s2, h3t1, h3t2, h3o, h3eq, hreg3⟩ :=
    loop_aux ((a.stacks s1).length + (a.stacks s2).length) (a.stacks s1) (a.stacks s2) a₂
      (by rw [ha2s]) (by rw [ha2s]) le_rfl ha2l
  obtain ⟨n₄, b₄, e₄, hn₄, h4t1, h4s1, h4o, hreg4, h4eq, _, _⟩ := revMove_eval h1t1.symm b₃
  have h4t2 : b₄.stacks tmp2 = b₃.stacks tmp2 := h4o tmp2 ht12.symm h1t2.symm
  have h4s2 : b₄.stacks s2 = [] := (h4o s2 h2t1 h12.symm).trans h3s2
  obtain ⟨n₅, b₅, e₅, hn₅, h5t2, h5s2, h5o, hreg5, h5eq, _, _⟩ := revMove_eval h2t2.symm b₄
  refine ⟨1 + (3 + (n₃ + (n₄ + n₅))), b₅,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ?_, ?_, ?_⟩
  · have ht1_len : (b₃.stacks tmp1).length = (a.stacks s1).length := by
      rw [h3t1, ha2s, ht1, List.append_nil, List.length_reverse]
    have ht2_len : (b₄.stacks tmp2).length = (a.stacks s2).length := by
      rw [h4t2, h3t2, ha2s, ht2, List.append_nil, List.length_reverse]
    rw [hn₄, hn₅, ht1_len, ht2_len]
    omega
  · funext k
    by_cases hk1 : k = s1
    · subst hk1; rw [h5o _ h1t2 h12, h4s1, h3s1, h3t1, ha2s, ht1]; simp
    · by_cases hk2 : k = s2
      · subst hk2; rw [h5s2, h4s2, h4t2, h3t2, ha2s, ht2]; simp
      · by_cases hkt1 : k = tmp1
        · subst hkt1; rw [h5o _ ht12 h2t1.symm, h4t1]; exact ht1.symm
        · by_cases hkt2 : k = tmp2
          · subst hkt2; rw [h5t2]; exact ht2.symm
          · rw [h5o k hkt2 hk2, h4o k hkt1 hk1, h3o k hk1 hk2 hkt1 hkt2, ha2s]
  · rw [h5eq, h4eq, h3eq, ha2_eq]; simp
  · exact regPreserved_trans
      (regPreserved_update _ _ (by decide) (by decide) (by decide))
      (regPreserved_trans hreg2 (regPreserved_trans hreg3 (regPreserved_trans hreg4 hreg5)))

/-- 9. Non-destructive `toNat s1 ≥ toNat s2` into `rCmp` (`tmp1, tmp2` empty before/after). -/
def cmpGEBody (s1 s2 tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    popBothBackup s1 s2 tmp1 tmp2,
    mkAtom (.bnot rTmp1 rVal2),
    mkAtom (.band rTmp1 rVal rTmp1),
    mkAtom (.bxor rTmp2 rVal rVal2),
    mkAtom (.bnot rTmp2 rTmp2),
    mkAtom (.band rTmp2 rTmp2 rCmp),
    mkAtom (.bor rCmp rTmp1 rTmp2),
    peekOrCond s1 s2
  ]

def cmpGE (s1 s2 tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.set rCmp true),
    peekOrCond s1 s2,
    mkWhile rLoop (cmpGEBody s1 s2 tmp1 tmp2),
    revMove tmp1 s1,
    revMove tmp2 s2
  ]

theorem cmpGE_eval {s1 s2 tmp1 tmp2 : Fin S}
    (h12 : s1 ≠ s2) (h1t1 : s1 ≠ tmp1) (h1t2 : s1 ≠ tmp2)
    (h2t1 : s2 ≠ tmp1) (h2t2 : s2 ≠ tmp2) (ht12 : tmp1 ≠ tmp2)
    (a : SState) (ht1 : a.stacks tmp1 = []) (ht2 : a.stacks tmp2 = []) :
    ∃ n b, StructuredCalls.Eval (cmpGE s1 s2 tmp1 tmp2) n a b ∧
      n ≤ 27 * ((a.stacks s1).length + (a.stacks s2).length) + 12 ∧
      b.stacks = a.stacks ∧
      b.regs rCmp = decide (BinaryArithmetic.toNat (a.stacks s2) ≤ BinaryArithmetic.toNat (a.stacks s1)) ∧
      RegPreserved a b := by
  have loop_aux : ∀ m xs ys x0,
      x0.stacks s1 = xs → x0.stacks s2 = ys → xs.length + ys.length ≤ m →
      x0.regs rLoop = (!xs.isEmpty || !ys.isEmpty) →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop (cmpGEBody s1 s2 tmp1 tmp2)) n x0 b ∧
        n ≤ 16 * (xs.length + ys.length) + 1 ∧
        b.stacks s1 = [] ∧ b.stacks s2 = [] ∧
        b.stacks tmp1 = xs.reverse ++ x0.stacks tmp1 ∧
        b.stacks tmp2 = ys.reverse ++ x0.stacks tmp2 ∧
        (∀ k, k ≠ s1 → k ≠ s2 → k ≠ tmp1 → k ≠ tmp2 → b.stacks k = x0.stacks k) ∧
        b.regs rCmp = cmpBitsAux xs ys (x0.regs rCmp) ∧ RegPreserved x0 b := by
    intro m
    induction m with
    | zero =>
        intro xs ys x0 hxs hys hm hhl
        have hnil1 : xs = [] := List.length_eq_zero_iff.mp (by omega)
        have hnil2 : ys = [] := List.length_eq_zero_iff.mp (by omega)
        subst hnil1; subst hnil2
        simp at hhl
        exact ⟨1, x0, .while_false hhl, by omega, hxs, hys, by simp, by simp,
          fun _ _ _ _ _ => rfl, by simp [cmpBitsAux], regPreserved_refl x0⟩
    | succ m ih =>
        intro xs ys x0 hxs hys hm hhl
        by_cases hdone : xs = [] ∧ ys = []
        · rcases hdone with ⟨rfl, rfl⟩
          simp at hhl
          exact ⟨1, x0, .while_false hhl, by omega, hxs, hys, by simp, by simp,
            fun _ _ _ _ _ => rfl, by simp [cmpBitsAux], regPreserved_refl x0⟩
        · have hloop_t : x0.regs rLoop = true := by
            rw [hhl]
            cases xs with
            | nil =>
                cases ys with
                | nil => exact False.elim (hdone ⟨rfl, rfl⟩)
                | cons _ _ => rfl
            | cons _ _ => rfl
          obtain ⟨nb, b₁, eb₁, hnb₁, hbs1, hbs2, hbt1, hbt2, hbo, hv1, hp1, hv2, hp2,
            _, hcmp1, _, hreg1⟩ := popBothBackup_eval h12 h1t1 h1t2 h2t1 h2t2 ht12 x0
          let b₂ : SState := ⟨Function.update b₁.regs rTmp1 (!(b₁.regs rVal2)), b₁.stacks⟩
          have e₂ := eval_bnot b₁ rTmp1 rVal2
          let b₃ : SState := ⟨Function.update b₂.regs rTmp1 (b₂.regs rVal && b₂.regs rTmp1), b₂.stacks⟩
          have e₃ := eval_band b₂ rTmp1 rVal rTmp1
          let b₄ : SState := ⟨Function.update b₃.regs rTmp2 (b₃.regs rVal ^^ b₃.regs rVal2), b₃.stacks⟩
          have e₄ := eval_bxor b₃ rTmp2 rVal rVal2
          let b₅ : SState := ⟨Function.update b₄.regs rTmp2 (!(b₄.regs rTmp2)), b₄.stacks⟩
          have e₅ := eval_bnot b₄ rTmp2 rTmp2
          let b₆ : SState := ⟨Function.update b₅.regs rTmp2 (b₅.regs rTmp2 && b₅.regs rCmp), b₅.stacks⟩
          have e₆ := eval_band b₅ rTmp2 rTmp2 rCmp
          let b₇ : SState := ⟨Function.update b₆.regs rCmp (b₆.regs rTmp1 || b₆.regs rTmp2), b₆.stacks⟩
          have e₇ := eval_bor b₆ rCmp rTmp1 rTmp2
          obtain ⟨b₈, e₈, hb8s, hb8l, _, hb8cmp, _, hreg8⟩ := peekOrCond_eval s1 s2 b₇
          have hstep_len : xs.tail.length + ys.tail.length ≤ m := by
            cases xs <;> cases ys <;> simp at hm hdone ⊢ <;> omega
          have hbody : StructuredCalls.Eval (cmpGEBody s1 s2 tmp1 tmp2) (nb + 9) x0 b₈ := by
            have := StructuredCalls.Eval.seq eb₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
            simpa [cmpGEBody, mkSeqList, mkSeq, Nat.add_assoc] using this
          have hb8_s1 : b₈.stacks s1 = xs.tail := by rw [hb8s, hbs1, hxs]
          have hb8_s2 : b₈.stacks s2 = ys.tail := by rw [hb8s, hbs2, hys]
          obtain ⟨nt, fin, htail, hnt, hfs1, hfs2, hft1, hft2, hfo, hfcmp, hreg_tail⟩ :=
            ih xs.tail ys.tail b₈ hb8_s1 hb8_s2 hstep_len
              (by rw [← hb8s, hb8_s1, hb8_s2] at hb8l; exact hb8l)
          have hbit_cmp : b₈.regs rCmp =
              ((b₁.regs rVal && !b₁.regs rVal2) ||
               (!(b₁.regs rVal ^^ b₁.regs rVal2) && x0.regs rCmp)) := by
            simp only [hb8cmp, b₇, b₆, b₅, b₄, b₃, b₂, hcmp1, Function.update, Fin.ext_iff]
            norm_num
          have hstep_aux : cmpBitsAux xs.tail ys.tail
              ((b₁.regs rVal && !b₁.regs rVal2) ||
               (!(b₁.regs rVal ^^ b₁.regs rVal2) && x0.regs rCmp)) =
              cmpBitsAux xs ys (x0.regs rCmp) := by
            rw [hv1, hv2, hxs, hys]
            cases xs with
            | nil =>
                cases ys with
                | nil => exact (hdone ⟨rfl, rfl⟩).elim
                | cons b bs => simp [cmpBitsAux]
            | cons a as =>
                cases ys with
                | nil => cases a <;> simp [cmpBitsAux]
                | cons b bs => simp [cmpBitsAux]
          refine ⟨nb + 9 + nt + 1, fin, .while_true hloop_t hbody htail, ?_, hfs1, hfs2, ?_, ?_, ?_, ?_, ?_⟩
          · have hdrop_le : xs.tail.length + ys.tail.length + 1 ≤ xs.length + ys.length := by
              cases xs <;> cases ys <;> simp at hdone ⊢ <;> omega
            omega
          · rw [hft1, hb8s, hbt1, hxs]; cases xs <;> simp
          · rw [hft2, hb8s, hbt2, hys]; cases ys <;> simp
          · intro k hk1 hk2 hkt1 hkt2
            rw [hfo k hk1 hk2 hkt1 hkt2, hb8s, hbo k hk1 hk2 hkt1 hkt2]
          · rw [hfcmp, hbit_cmp, hstep_aux]
          · exact regPreserved_trans hreg1
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
                (regPreserved_trans hreg8 hreg_tail)))))))
  let a₁ : SState := ⟨Function.update a.regs rCmp true, a.stacks⟩
  have e₁ := eval_set a rCmp true
  obtain ⟨a₂, e₂, ha2s, ha2l, _, ha2cmp, _, hreg2⟩ := peekOrCond_eval s1 s2 a₁
  have ha2_cmp : a₂.regs rCmp = true := by rw [ha2cmp]; simp [a₁]
  obtain ⟨n₃, b₃, e₃, hn₃, h3s1, h3s2, h3t1, h3t2, h3o, h3cmp, hreg3⟩ :=
    loop_aux ((a.stacks s1).length + (a.stacks s2).length) (a.stacks s1) (a.stacks s2) a₂
      (by rw [ha2s]) (by rw [ha2s]) le_rfl ha2l
  obtain ⟨n₄, b₄, e₄, hn₄, h4t1, h4s1, h4o, hreg4, _, h4cmp, _⟩ := revMove_eval h1t1.symm b₃
  have h4t2 : b₄.stacks tmp2 = b₃.stacks tmp2 := h4o tmp2 ht12.symm h1t2.symm
  have h4s2 : b₄.stacks s2 = [] := (h4o s2 h2t1 h12.symm).trans h3s2
  obtain ⟨n₅, b₅, e₅, hn₅, h5t2, h5s2, h5o, hreg5, _, h5cmp, _⟩ := revMove_eval h2t2.symm b₄
  refine ⟨1 + (3 + (n₃ + (n₄ + n₅))), b₅,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ?_, ?_, ?_⟩
  · have ht1_len : (b₃.stacks tmp1).length = (a.stacks s1).length := by
      rw [h3t1, ha2s, ht1, List.append_nil, List.length_reverse]
    have ht2_len : (b₄.stacks tmp2).length = (a.stacks s2).length := by
      rw [h4t2, h3t2, ha2s, ht2, List.append_nil, List.length_reverse]
    rw [hn₄, hn₅, ht1_len, ht2_len]
    omega
  · funext k
    by_cases hk1 : k = s1
    · subst hk1; rw [h5o _ h1t2 h12, h4s1, h3s1, h3t1, ha2s, ht1]; simp
    · by_cases hk2 : k = s2
      · subst hk2; rw [h5s2, h4s2, h4t2, h3t2, ha2s, ht2]; simp
      · by_cases hkt1 : k = tmp1
        · subst hkt1; rw [h5o _ ht12 h2t1.symm, h4t1]; exact ht1.symm
        · by_cases hkt2 : k = tmp2
          · subst hkt2; rw [h5t2]; exact ht2.symm
          · rw [h5o k hkt2 hk2, h4o k hkt1 hk1, h3o k hk1 hk2 hkt1 hkt2, ha2s]
  · rw [h5cmp, h4cmp, h3cmp, ha2_cmp, cmpBitsAux_correct]
    split_ifs with hlt1 hlt2
    · symm; exact decide_eq_true (Nat.le_of_lt hlt1)
    · symm; exact decide_eq_false (by omega)
    · symm; exact decide_eq_true (by omega)
  · exact regPreserved_trans
      (regPreserved_update _ _ (by decide) (by decide) (by decide))
      (regPreserved_trans hreg2 (regPreserved_trans hreg3 (regPreserved_trans hreg4 hreg5)))

/-- 10. In-place addition `dst := (toNat dst + toNat s).bits`, preserving `s` (`tmp1, tmp2` empty). -/
def addCond (dst s : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.peek dst rTmp1 rPres),
    mkAtom (.peek s rTmp2 rPres2),
    mkAtom (.bor rTmp1 rPres rPres2),
    mkAtom (.bor rLoop rTmp1 rCarry)
  ]

def addInPlaceBody (dst s tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.pop dst rVal rPres),
    mkAtom (.pop s rVal2 rPres2),
    mkIte rPres2 (mkAtom (.push tmp1 rVal2)) mkSkip,
    mkAtom (.bxor rBit rVal rVal2),
    mkAtom (.bxor rBit rBit rCarry),
    mkAtom (.push tmp2 rBit),
    mkAtom (.bxor rTmp1 rVal rVal2),
    mkAtom (.band rTmp1 rTmp1 rCarry),
    mkAtom (.band rTmp2 rVal rVal2),
    mkAtom (.bor rCarry rTmp1 rTmp2),
    addCond dst s
  ]

def addInPlace (dst s tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.set rCarry false),
    addCond dst s,
    mkWhile rLoop (addInPlaceBody dst s tmp1 tmp2),
    revMove tmp1 s,
    popLeadingFalse tmp2,
    revMove tmp2 dst
  ]

theorem addCond_eval (dst s : Fin S) (x : SState) :
    ∃ y, StructuredCalls.Eval (addCond dst s) 4 x y ∧
      y.stacks = x.stacks ∧
      y.regs rLoop = (!(x.stacks dst).isEmpty || !(x.stacks s).isEmpty || x.regs rCarry) ∧
      y.regs rCarry = x.regs rCarry ∧ RegPreserved x y := by
  let y₁ : SState := ⟨BitProgram.readRegs x.regs rTmp1 rPres (x.stacks dst).head?, x.stacks⟩
  have e₁ := eval_peek x dst rTmp1 rPres
  let y₂ : SState := ⟨BitProgram.readRegs y₁.regs rTmp2 rPres2 (x.stacks s).head?, x.stacks⟩
  have e₂ : StructuredCalls.Eval (mkAtom (.peek s rTmp2 rPres2)) 1 y₁ y₂ := eval_peek y₁ s rTmp2 rPres2
  let y₃ : SState := ⟨Function.update y₂.regs rTmp1 (y₂.regs rPres || y₂.regs rPres2), x.stacks⟩
  have e₃ := eval_bor y₂ rTmp1 rPres rPres2
  let y₄ : SState := ⟨Function.update y₃.regs rLoop (y₃.regs rTmp1 || y₃.regs rCarry), x.stacks⟩
  have e₄ := eval_bor y₃ rLoop rTmp1 rCarry
  refine ⟨y₄, .seq e₁ (.seq e₂ (.seq e₃ e₄)), rfl, ?_, ?_, ?_⟩
  · simp only [y₄, y₃, y₂, y₁, BitProgram.readRegs, Function.update, Fin.ext_iff]
    norm_num
    cases x.stacks dst <;> cases x.stacks s <;> cases x.regs rCarry <;> rfl
  · simp only [y₄, y₃, y₂, y₁, BitProgram.readRegs, Function.update, Fin.ext_iff]
    norm_num
  · exact regPreserved_trans
      (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (regPreserved_trans
        (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (regPreserved_trans
          (regPreserved_update _ _ (by decide) (by decide) (by decide))
          (regPreserved_update _ _ (by decide) (by decide) (by decide))))

theorem add_bit_step_id (a b c : Bool) :
    bitVal a + bitVal b + bitVal c =
      bitVal (xor (xor a b) c) + 2 * bitVal ((xor a b && c) || (a && b)) := by
  cases a <;> cases b <;> cases c <;> decide

theorem addInPlace_eval {dst s tmp1 tmp2 : Fin S}
    (h12 : dst ≠ s) (h1t1 : dst ≠ tmp1) (h1t2 : dst ≠ tmp2)
    (h2t1 : s ≠ tmp1) (h2t2 : s ≠ tmp2) (ht12 : tmp1 ≠ tmp2)
    (a : SState) (ht1 : a.stacks tmp1 = []) (ht2 : a.stacks tmp2 = []) :
    ∃ n b, StructuredCalls.Eval (addInPlace dst s tmp1 tmp2) n a b ∧
      n ≤ 34 * ((a.stacks dst).length + (a.stacks s).length + 1) + 18 ∧
      b.stacks dst = (BinaryArithmetic.toNat (a.stacks dst) + BinaryArithmetic.toNat (a.stacks s)).bits ∧
      b.stacks s = a.stacks s ∧ b.stacks tmp1 = [] ∧ b.stacks tmp2 = [] ∧
      (∀ k, k ≠ dst → k ≠ s → k ≠ tmp1 → k ≠ tmp2 → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  have loop_aux : ∀ m xs ys zs c x0,
      x0.stacks dst = xs → x0.stacks s = ys → x0.stacks tmp2 = zs → x0.regs rCarry = c →
      xs.length + ys.length + bitVal c ≤ m →
      x0.regs rLoop = (!xs.isEmpty || !ys.isEmpty || c) →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop (addInPlaceBody dst s tmp1 tmp2)) n x0 b ∧
        n ≤ 16 * (xs.length + ys.length + bitVal c) + 1 ∧
        b.stacks dst = [] ∧ b.stacks s = [] ∧
        b.stacks tmp1 = ys.reverse ++ x0.stacks tmp1 ∧
        (∃ zs', b.stacks tmp2 = zs' ∧ zs'.length ≤ zs.length + xs.length + ys.length + bitVal c ∧
          BinaryArithmetic.toNat zs'.reverse =
            BinaryArithmetic.toNat zs.reverse +
              2 ^ zs.length * (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys + bitVal c)) ∧
        (∀ k, k ≠ dst → k ≠ s → k ≠ tmp1 → k ≠ tmp2 → b.stacks k = x0.stacks k) ∧
        RegPreserved x0 b := by
    intro m
    induction m with
    | zero =>
        intro xs ys zs c x0 hxs hys hzs hc hm hhl
        have hnil1 : xs = [] := List.length_eq_zero_iff.mp (by omega)
        have hnil2 : ys = [] := List.length_eq_zero_iff.mp (by omega)
        have hcf : c = false := by cases c <;> simp at hm <;> rfl
        subst hnil1; subst hnil2; subst hcf
        simp at hhl
        exact ⟨1, x0, .while_false hhl, by omega, hxs, hys, by simp,
          ⟨zs, hzs, by simp, by simp [BinaryArithmetic.toNat]⟩,
          fun _ _ _ _ _ => rfl, regPreserved_refl x0⟩
    | succ m ih =>
        intro xs ys zs c x0 hxs hys hzs hc hm hhl
        by_cases hdone : xs = [] ∧ ys = [] ∧ c = false
        · rcases hdone with ⟨rfl, rfl, rfl⟩
          simp at hhl
          exact ⟨1, x0, .while_false hhl, by omega, hxs, hys, by simp,
            ⟨zs, hzs, by simp, by simp [BinaryArithmetic.toNat]⟩,
            fun _ _ _ _ _ => rfl, regPreserved_refl x0⟩
        · have hloop_t : x0.regs rLoop = true := by
            rw [hhl]
            cases xs with
            | nil =>
                cases ys with
                | nil =>
                    cases c with
                    | false => exact False.elim (hdone ⟨rfl, rfl, rfl⟩)
                    | true => rfl
                | cons _ _ => rfl
            | cons _ _ => rfl
          let x₁ : SState := ⟨BitProgram.readRegs x0.regs rVal rPres (x0.stacks dst).head?,
            Function.update x0.stacks dst xs.tail⟩
          have e₁ : StructuredCalls.Eval (mkAtom (.pop dst rVal rPres)) 1 x0 x₁ := by
            simpa [x₁, hxs] using eval_pop x0 dst rVal rPres
          let x₂ : SState := ⟨BitProgram.readRegs x₁.regs rVal2 rPres2 ys.head?,
            Function.update x₁.stacks s ys.tail⟩
          have e₂ : StructuredCalls.Eval (mkAtom (.pop s rVal2 rPres2)) 1 x₁ x₂ := by
            have hs1 : x₁.stacks s = ys := by simp [x₁, Function.update_of_ne h12.symm, hys]
            simpa [x₂, hs1] using eval_pop x₁ s rVal2 rPres2
          have hpart : ∃ n₃ x₃, StructuredCalls.Eval
              (mkIte rPres2 (mkAtom (.push tmp1 rVal2)) mkSkip) n₃ x₂ x₃ ∧ n₃ ≤ 2 ∧
              x₃.regs = x₂.regs ∧ x₃.stacks dst = xs.tail ∧ x₃.stacks s = ys.tail ∧
              x₃.stacks tmp1 = (match ys with | [] => x0.stacks tmp1 | y :: _ => y :: x0.stacks tmp1) ∧
              x₃.stacks tmp2 = zs ∧
              (∀ k, k ≠ dst → k ≠ s → k ≠ tmp1 → k ≠ tmp2 → x₃.stacks k = x0.stacks k) := by
            cases ys with
            | nil =>
                have hp2 : x₂.regs rPres2 = false := by simp [x₂, readRegs_eq_pres]
                refine ⟨1, x₂, .ite_false hp2 (.base (.skip x₂)), by omega, rfl,
                  by simp [x₂, x₁, Function.update_of_ne h12],
                  by simp [x₂],
                  by simp [x₂, x₁, Function.update_of_ne h2t1.symm, Function.update_of_ne h1t1.symm],
                  by simp [x₂, x₁, Function.update_of_ne h2t2.symm, Function.update_of_ne h1t2.symm, hzs],
                  fun k hk1 hk2 hkt1 hkt2 => by
                    simp [x₂, x₁, Function.update_of_ne hk2, Function.update_of_ne hk1]⟩
            | cons y rest =>
                have hp2 : x₂.regs rPres2 = true := by simp [x₂, readRegs_eq_pres]
                have hv2 : x₂.regs rVal2 = y := by
                  dsimp only [x₂]; rw [readRegs_eq_val (by decide : rVal2 ≠ rPres2)]; rfl
                let x₃ : SState := ⟨x₂.regs, Function.update x₂.stacks tmp1 (y :: x0.stacks tmp1)⟩
                have e₃ : StructuredCalls.Eval (mkAtom (.push tmp1 rVal2)) 1 x₂ x₃ := by
                  have ht : x₂.stacks tmp1 = x0.stacks tmp1 := by
                    simp [x₂, x₁, Function.update_of_ne h2t1.symm, Function.update_of_ne h1t1.symm]
                  have ep := eval_push x₂ tmp1 rVal2
                  rw [hv2, ht] at ep
                  exact ep
                refine ⟨2, x₃, .ite_true hp2 e₃, by omega, rfl,
                  by simp [x₃, x₂, x₁, Function.update_of_ne h1t1, Function.update_of_ne h12],
                  by simp [x₃, x₂, Function.update_of_ne h2t1],
                  by simp [x₃],
                  by simp [x₃, x₂, x₁, Function.update_of_ne ht12.symm, Function.update_of_ne h2t2.symm,
                    Function.update_of_ne h1t2.symm, hzs],
                  fun k hk1 hk2 hkt1 hkt2 => by
                    simp [x₃, x₂, x₁, Function.update_of_ne hkt1, Function.update_of_ne hk2,
                      Function.update_of_ne hk1]⟩
          obtain ⟨n₃, x₃, e₃, hn₃, hx3r, hx3d, hx3s, hx3t1, hx3t2, hx3o⟩ := hpart
          have hva : x₃.regs rVal = xs.head?.getD false := by
            rw [hx3r]; dsimp only [x₂, x₁]
            rw [readRegs_eq_other (by decide) (by decide),
              readRegs_eq_val (by decide : rVal ≠ rPres), hxs]
          have hvb : x₃.regs rVal2 = ys.head?.getD false := by
            rw [hx3r]; dsimp only [x₂]
            rw [readRegs_eq_val (by decide : rVal2 ≠ rPres2)]
          have hvc : x₃.regs rCarry = c := by
            rw [hx3r]; dsimp only [x₂, x₁]
            rw [readRegs_eq_other (by decide) (by decide),
              readRegs_eq_other (by decide) (by decide), hc]
          let aBit := xs.head?.getD false
          let bBit := ys.head?.getD false
          let bitOut := xor (xor aBit bBit) c
          let cNext := (xor aBit bBit && c) || (aBit && bBit)
          let x₄ : SState := ⟨Function.update x₃.regs rBit (x₃.regs rVal ^^ x₃.regs rVal2), x₃.stacks⟩
          have e₄ := eval_bxor x₃ rBit rVal rVal2
          let x₅ : SState := ⟨Function.update x₄.regs rBit (x₄.regs rBit ^^ x₄.regs rCarry), x₄.stacks⟩
          have e₅ := eval_bxor x₄ rBit rBit rCarry
          let x₆ : SState := ⟨x₅.regs, Function.update x₅.stacks tmp2 (x₅.regs rBit :: x₅.stacks tmp2)⟩
          have e₆ := eval_push x₅ tmp2 rBit
          let x₇ : SState := ⟨Function.update x₆.regs rTmp1 (x₆.regs rVal ^^ x₆.regs rVal2), x₆.stacks⟩
          have e₇ := eval_bxor x₆ rTmp1 rVal rVal2
          let x₈ : SState := ⟨Function.update x₇.regs rTmp1 (x₇.regs rTmp1 && x₇.regs rCarry), x₇.stacks⟩
          have e₈ := eval_band x₇ rTmp1 rTmp1 rCarry
          let x₉ : SState := ⟨Function.update x₈.regs rTmp2 (x₈.regs rVal && x₈.regs rVal2), x₈.stacks⟩
          have e₉ := eval_band x₈ rTmp2 rVal rVal2
          let x₁₀ : SState := ⟨Function.update x₉.regs rCarry (x₉.regs rTmp1 || x₉.regs rTmp2), x₉.stacks⟩
          have e₁₀ := eval_bor x₉ rCarry rTmp1 rTmp2
          obtain ⟨x₁₁, e₁₁, hx11s, hx11l, hx11c, hreg11⟩ := addCond_eval dst s x₁₀
          have hx10_bit : x₅.regs rBit = bitOut := by
            simp only [x₅, x₄, Function.update, Fin.ext_iff]
            norm_num
            rw [show (0 : Fin R) = rVal from rfl, hva, hvb, hvc]
            dsimp only [bitOut, aBit, bBit]
            cases xs.head?.getD false <;> cases ys.head?.getD false <;> cases c <;> rfl
          have hx10_carry : x₁₀.regs rCarry = cNext := by
            simp only [x₁₀, x₉, x₈, x₇, x₆, x₅, x₄, Function.update, Fin.ext_iff]
            norm_num
            change ((x₃.regs rVal ^^ x₃.regs rVal2) && x₃.regs rCarry || x₃.regs rVal && x₃.regs rVal2) = cNext
            rw [hva, hvb, hvc]
          have hx11_dst : x₁₁.stacks dst = xs.tail := by
            rw [hx11s]; dsimp only [x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_of_ne h1t2, hx3d]
          have hx11_s : x₁₁.stacks s = ys.tail := by
            rw [hx11s]; dsimp only [x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_of_ne h2t2, hx3s]
          have hx11_t2 : x₁₁.stacks tmp2 = bitOut :: zs := by
            rw [hx11s]; dsimp only [x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_self, hx10_bit, show x₅.stacks tmp2 = zs from hx3t2]
          have hd_drop : xs.tail.length + ys.tail.length + bitVal cNext + 1 ≤
              xs.length + ys.length + bitVal c := by
            cases xs with
            | nil =>
                cases ys with
                | nil =>
                    have hct : c = true := by
                      by_contra hcf; apply hdone; exact ⟨rfl, rfl, Bool.eq_false_iff.mpr hcf⟩
                    subst hct; simp [cNext, aBit, bBit]
                | cons y ys' =>
                    cases y <;> cases c <;> simp [List.length_cons, cNext, aBit, bBit] <;> omega
            | cons x xs' =>
                cases ys with
                | nil => cases x <;> cases c <;> simp [List.length_cons, cNext, aBit, bBit] <;> omega
                | cons y ys' =>
                    cases x <;> cases y <;> cases c <;> simp [List.length_cons, cNext, aBit, bBit] <;> omega
          have hmeas : xs.tail.length + ys.tail.length + bitVal cNext ≤ m := by omega
          have hbody : StructuredCalls.Eval (addInPlaceBody dst s tmp1 tmp2) (n₃ + 13) x0 x₁₁ := by
            have hstep_cnt : 1 + (1 + (n₃ + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 4))))))))) = n₃ + 13 := by omega
            rw [← hstep_cnt]
            exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅
              (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉ (.seq e₁₀ e₁₁)))))))))
          obtain ⟨nt, fin, htail, hnt, hfd, hfs, hft1, ⟨zs', hft2, hzs_len, hzs_val⟩, hfo, hreg_tail⟩ :=
            ih xs.tail ys.tail (bitOut :: zs) cNext x₁₁ hx11_dst hx11_s hx11_t2
              (hx11c.trans hx10_carry) hmeas
              (by rw [← hx11s, hx11_dst, hx11_s, hx10_carry] at hx11l; exact hx11l)
          have hsum_step :
              BinaryArithmetic.toNat (bitOut :: zs).reverse +
                2 ^ (bitOut :: zs).length *
                  (BinaryArithmetic.toNat xs.tail + BinaryArithmetic.toNat ys.tail + bitVal cNext) =
              BinaryArithmetic.toNat zs.reverse +
                2 ^ zs.length * (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys + bitVal c) := by
            simp only [List.reverse_cons, toNat_append, List.length_cons, List.length_reverse,
              BinaryArithmetic.toNat, mul_zero, add_zero, pow_succ']
            have hxs_eq : BinaryArithmetic.toNat xs = bitVal aBit + 2 * BinaryArithmetic.toNat xs.tail := by
              cases xs <;> simp [BinaryArithmetic.toNat, aBit]
            have hys_eq : BinaryArithmetic.toNat ys = bitVal bBit + 2 * BinaryArithmetic.toNat ys.tail := by
              cases ys <;> simp [BinaryArithmetic.toNat, bBit]
            have hbit := add_bit_step_id aBit bBit c
            change _ = bitVal bitOut + 2 * bitVal cNext at hbit
            rw [hxs_eq, hys_eq]
            have hpow : BinaryArithmetic.toNat zs.reverse + 2 ^ zs.length * bitVal bitOut +
                (2 * 2 ^ zs.length) * (BinaryArithmetic.toNat xs.tail + BinaryArithmetic.toNat ys.tail + bitVal cNext) =
                BinaryArithmetic.toNat zs.reverse + 2 ^ zs.length *
                  ((bitVal bitOut + 2 * bitVal cNext) +
                    2 * BinaryArithmetic.toNat xs.tail + 2 * BinaryArithmetic.toNat ys.tail) := by ring
            rw [hpow, ← hbit]
            ring
          have hzs_len' : zs'.length ≤ zs.length + xs.length + ys.length + bitVal c := by
            simp only [List.length_cons] at hzs_len
            omega
          refine ⟨n₃ + 13 + nt + 1, fin, .while_true hloop_t hbody htail, by omega, hfd, hfs, ?_,
            ⟨zs', hft2, hzs_len', by rw [hzs_val, hsum_step]⟩, ?_, ?_⟩
          · rw [hft1, hx11s]; dsimp only [x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_of_ne ht12, hx3t1]; cases ys <;> simp
          · intro k hk1 hk2 hkt1 hkt2
            rw [hfo k hk1 hk2 hkt1 hkt2, hx11s]; dsimp only [x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_of_ne hkt2, hx3o k hk1 hk2 hkt1 hkt2]
          · have hreg_pre : RegPreserved x0 x₃ := by
              have hr1 := regPreserved_readRegs (a := x0) (v := rVal) (p := rPres)
                (x0.stacks dst).head? x₁.stacks (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide)
              have hr2 := regPreserved_readRegs (a := x₁) (v := rVal2) (p := rPres2)
                ys.head? x₂.stacks (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide)
              have hr3 : RegPreserved x₂ x₃ := by simp [RegPreserved, hx3r]
              exact regPreserved_trans hr1 (regPreserved_trans hr2 hr3)
            exact regPreserved_trans hreg_pre
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
                (regPreserved_trans hreg11 hreg_tail)))))))
  let a₁ : SState := ⟨Function.update a.regs rCarry false, a.stacks⟩
  have e₁ := eval_set a rCarry false
  obtain ⟨a₂, e₂, ha2s, ha2l, ha2c, hreg2⟩ := addCond_eval dst s a₁
  have ha2_c : a₂.regs rCarry = false := by rw [ha2c]; simp [a₁]
  obtain ⟨n₃, b₃, e₃, hn₃, h3d, h3s, h3t1, ⟨zs', h3t2, hzs_len, hzs_val⟩, h3o, hreg3⟩ :=
    loop_aux ((a.stacks dst).length + (a.stacks s).length + 0) (a.stacks dst) (a.stacks s) [] false a₂
      (by rw [ha2s]) (by rw [ha2s]) (by rw [ha2s, ht2]) ha2_c le_rfl
      (by simpa [a₁] using ha2l)
  obtain ⟨n₄, b₄, e₄, hn₄, h4t1, h4s, h4o, hreg4, _, _, _⟩ := revMove_eval h2t1.symm b₃
  have h4d : b₄.stacks dst = [] := (h4o dst h1t1 h12).trans h3d
  have h4t2 : b₄.stacks tmp2 = zs' := (h4o tmp2 ht12.symm h2t2.symm).trans h3t2
  obtain ⟨n₅, b₅, e₅, hn₅, h5t2, h5o, hreg5⟩ := popLeadingFalse_eval tmp2 b₄
  have h5d : b₅.stacks dst = [] := (h5o dst h1t2).trans h4d
  have h5s : b₅.stacks s = a.stacks s := by
    rw [h5o s h2t2, h4s, h3s, h3t1, ha2s, ht1]; simp
  have h5t1 : b₅.stacks tmp1 = [] := (h5o tmp1 ht12).trans h4t1
  obtain ⟨n₆, b₆, e₆, hn₆, h6t2, h6d, h6o, hreg6, _, _, _⟩ := revMove_eval h1t2.symm b₅
  refine ⟨1 + (4 + (n₃ + (n₄ + (n₅ + n₆)))), b₆,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, ?_, ?_, ?_, h6t2, ?_, ?_⟩
  · have ht1_len : (b₃.stacks tmp1).length = (a.stacks s).length := by
      rw [h3t1, ha2s, ht1, List.append_nil, List.length_reverse]
    have ht2_len : zs'.length ≤ (a.stacks dst).length + (a.stacks s).length := by
      simp only [List.length_nil, zero_add, bitVal_false, add_zero] at hzs_len
      exact hzs_len
    have hstrip_len : (stripLeadingFalse zs').length ≤ zs'.length := by
      have hsr := congrArg List.length (stripLeadingFalse_reverse_eq zs'.reverse)
      simp only [List.reverse_reverse, List.length_reverse] at hsr
      have hlt := toNat_lt_two_pow zs'.reverse
      rw [List.length_reverse] at hlt
      rw [hsr]; exact bits_length_le_of_lt hlt
    simp only [bitVal_false, add_zero] at hn₃
    rw [h4t2] at hn₅
    rw [hn₄, hn₆, h5t2, h4t2, ht1_len]
    omega
  · rw [h6d, h5d, List.append_nil, h5t2, h4t2, ← List.reverse_reverse zs',
      stripLeadingFalse_reverse_eq, List.reverse_reverse]
    simp only [List.reverse_nil, BinaryArithmetic.toNat, List.length_nil, pow_zero, one_mul,
      bitVal_false, add_zero, zero_add] at hzs_val
    rw [hzs_val]
  · rw [h6o s h2t2 h12.symm, h5s]
  · rw [h6o tmp1 ht12 h1t1.symm, h5t1]
  · intro k hkd hks hkt1 hkt2
    rw [h6o k hkt2 hkd, h5o k hkt2, h4o k hkt1 hks, h3o k hkd hks hkt1 hkt2, ha2s]
  · exact regPreserved_trans
      (regPreserved_update _ _ (by decide) (by decide) (by decide))
      (regPreserved_trans hreg2 (regPreserved_trans hreg3
        (regPreserved_trans hreg4 (regPreserved_trans hreg5 hreg6))))

/-! ### Part B: `subInPlace`, `mulToCore`, `divModCore`, `mulMod`, `powModCmd` -/

def RangeCleared (lo hi : ℕ) (stk : Fin S → List Bool) : Prop :=
  ∀ k : Fin S, lo ≤ k.val → k.val ≤ hi → stk k = []

theorem rangeCleared_mono {lo₁ hi₁ lo₂ hi₂ : ℕ} {stk : Fin S → List Bool}
    (h : RangeCleared lo₁ hi₁ stk) (hlo : lo₁ ≤ lo₂) (hhi : hi₂ ≤ hi₁) :
    RangeCleared lo₂ hi₂ stk :=
  fun k hk1 hk2 => h k (hlo.trans hk1) (hk2.trans hhi)

theorem fin_ne_of_lt_ge (m : ℕ) {a b : Fin S} (ha : a.val < m) (hb : m ≤ b.val) : a ≠ b :=
  fun h => by subst h; omega

theorem fin_ne_of_val_ne {a b : Fin S} (h : a.val ≠ b.val) : a ≠ b :=
  fun heq => h (congrArg Fin.val heq)

/-- 11. In-place subtraction `dst := (toNat dst - toNat s).bits` assuming `toNat s ≤ toNat dst`. -/
theorem sub_bit_step_id (a b c : Bool) :
    (bitVal a : ℤ) - (bitVal b : ℤ) - (bitVal c : ℤ) =
      (bitVal (xor (xor a b) c) : ℤ) -
        2 * (bitVal ((!a && (b || c)) || (b && c)) : ℤ) := by
  cases a <;> cases b <;> cases c <;> decide

def subInPlaceBody (dst s tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.pop dst rVal rPres),
    mkAtom (.pop s rVal2 rPres2),
    mkIte rPres2 (mkAtom (.push tmp1 rVal2)) mkSkip,
    mkAtom (.bxor rBit rVal rVal2),
    mkAtom (.bxor rBit rBit rCarry),
    mkAtom (.push tmp2 rBit),
    mkAtom (.bnot rTmp1 rVal),
    mkAtom (.bor rTmp2 rVal2 rCarry),
    mkAtom (.band rTmp1 rTmp1 rTmp2),
    mkAtom (.band rTmp2 rVal2 rCarry),
    mkAtom (.bor rCarry rTmp1 rTmp2),
    peekOrCond dst s
  ]

def subInPlace (dst s tmp1 tmp2 : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.set rCarry false),
    peekOrCond dst s,
    mkWhile rLoop (subInPlaceBody dst s tmp1 tmp2),
    revMove tmp1 s,
    popLeadingFalse tmp2,
    revMove tmp2 dst
  ]

theorem subInPlace_eval {dst s tmp1 tmp2 : Fin S}
    (h12 : dst ≠ s) (h1t1 : dst ≠ tmp1) (h1t2 : dst ≠ tmp2)
    (h2t1 : s ≠ tmp1) (h2t2 : s ≠ tmp2) (ht12 : tmp1 ≠ tmp2)
    (a : SState) (ht1 : a.stacks tmp1 = []) (ht2 : a.stacks tmp2 = [])
    (hle : BinaryArithmetic.toNat (a.stacks s) ≤ BinaryArithmetic.toNat (a.stacks dst)) :
    ∃ n b, StructuredCalls.Eval (subInPlace dst s tmp1 tmp2) n a b ∧
      n ≤ 34 * ((a.stacks dst).length + (a.stacks s).length + 1) + 18 ∧
      b.stacks dst = (BinaryArithmetic.toNat (a.stacks dst) - BinaryArithmetic.toNat (a.stacks s)).bits ∧
      b.stacks s = a.stacks s ∧ b.stacks tmp1 = [] ∧ b.stacks tmp2 = [] ∧
      (∀ k, k ≠ dst → k ≠ s → k ≠ tmp1 → k ≠ tmp2 → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  have loop_aux : ∀ m xs ys zs c x0,
      x0.stacks dst = xs → x0.stacks s = ys → x0.stacks tmp2 = zs → x0.regs rCarry = c →
      xs.length + ys.length ≤ m →
      x0.regs rLoop = (!xs.isEmpty || !ys.isEmpty) →
      BinaryArithmetic.toNat ys + bitVal c ≤ BinaryArithmetic.toNat xs →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop (subInPlaceBody dst s tmp1 tmp2)) n x0 b ∧
        n ≤ 16 * (xs.length + ys.length) + 1 ∧
        b.stacks dst = [] ∧ b.stacks s = [] ∧
        b.stacks tmp1 = ys.reverse ++ x0.stacks tmp1 ∧
        (∃ zs', b.stacks tmp2 = zs' ∧ zs'.length ≤ zs.length + xs.length + ys.length ∧
          ((BinaryArithmetic.toNat zs'.reverse : ℕ) : ℤ) =
            ((BinaryArithmetic.toNat zs.reverse : ℕ) : ℤ) +
              (2 : ℤ) ^ zs.length *
                (((BinaryArithmetic.toNat xs : ℕ) : ℤ) -
                  ((BinaryArithmetic.toNat ys : ℕ) : ℤ) - (bitVal c : ℤ))) ∧
        (∀ k, k ≠ dst → k ≠ s → k ≠ tmp1 → k ≠ tmp2 → b.stacks k = x0.stacks k) ∧
        RegPreserved x0 b := by
    intro m
    induction m with
    | zero =>
        intro xs ys zs c x0 hxs hys hzs hc hm hhl hge
        have hnil1 : xs = [] := List.length_eq_zero_iff.mp (by omega)
        have hnil2 : ys = [] := List.length_eq_zero_iff.mp (by omega)
        subst hnil1; subst hnil2
        have hcf : c = false := by
          cases c with
          | false => rfl
          | true => simp [BinaryArithmetic.toNat] at hge
        subst hcf
        simp at hhl
        exact ⟨1, x0, .while_false hhl, by omega, hxs, hys, by simp,
          ⟨zs, hzs, by simp, by simp [BinaryArithmetic.toNat]⟩,
          fun _ _ _ _ _ => rfl, regPreserved_refl x0⟩
    | succ m ih =>
        intro xs ys zs c x0 hxs hys hzs hc hm hhl hge
        by_cases hdone : xs = [] ∧ ys = []
        · rcases hdone with ⟨rfl, rfl⟩
          have hcf : c = false := by
            cases c with
            | false => rfl
            | true => simp [BinaryArithmetic.toNat] at hge
          subst hcf
          simp at hhl
          exact ⟨1, x0, .while_false hhl, by omega, hxs, hys, by simp,
            ⟨zs, hzs, by simp, by simp [BinaryArithmetic.toNat]⟩,
            fun _ _ _ _ _ => rfl, regPreserved_refl x0⟩
        · have hloop_t : x0.regs rLoop = true := by
            rw [hhl]
            cases xs with
            | nil =>
                cases ys with
                | nil => exact False.elim (hdone ⟨rfl, rfl⟩)
                | cons _ _ => rfl
            | cons _ _ => rfl
          let x₁ : SState := ⟨BitProgram.readRegs x0.regs rVal rPres (x0.stacks dst).head?,
            Function.update x0.stacks dst xs.tail⟩
          have e₁ : StructuredCalls.Eval (mkAtom (.pop dst rVal rPres)) 1 x0 x₁ := by
            simpa [x₁, hxs] using eval_pop x0 dst rVal rPres
          let x₂ : SState := ⟨BitProgram.readRegs x₁.regs rVal2 rPres2 ys.head?,
            Function.update x₁.stacks s ys.tail⟩
          have e₂ : StructuredCalls.Eval (mkAtom (.pop s rVal2 rPres2)) 1 x₁ x₂ := by
            have hs1 : x₁.stacks s = ys := by simp [x₁, Function.update_of_ne h12.symm, hys]
            simpa [x₂, hs1] using eval_pop x₁ s rVal2 rPres2
          have hpart : ∃ n₃ x₃, StructuredCalls.Eval
              (mkIte rPres2 (mkAtom (.push tmp1 rVal2)) mkSkip) n₃ x₂ x₃ ∧ n₃ ≤ 2 ∧
              x₃.regs = x₂.regs ∧ x₃.stacks dst = xs.tail ∧ x₃.stacks s = ys.tail ∧
              x₃.stacks tmp1 = (match ys with | [] => x0.stacks tmp1 | y :: _ => y :: x0.stacks tmp1) ∧
              x₃.stacks tmp2 = zs ∧
              (∀ k, k ≠ dst → k ≠ s → k ≠ tmp1 → k ≠ tmp2 → x₃.stacks k = x0.stacks k) := by
            cases ys with
            | nil =>
                have hp2 : x₂.regs rPres2 = false := by simp [x₂]
                refine ⟨1, x₂, .ite_false hp2 (.base (.skip x₂)), by omega, rfl,
                  by simp [x₂, x₁, Function.update_of_ne h12],
                  by simp [x₂],
                  by simp [x₂, x₁, Function.update_of_ne h2t1.symm, Function.update_of_ne h1t1.symm],
                  by simp [x₂, x₁, Function.update_of_ne h2t2.symm, Function.update_of_ne h1t2.symm, hzs],
                  fun k hk1 hk2 hkt1 hkt2 => by
                    simp [x₂, x₁, Function.update_of_ne hk2, Function.update_of_ne hk1]⟩
            | cons y rest =>
                have hp2 : x₂.regs rPres2 = true := by simp [x₂]
                have hv2 : x₂.regs rVal2 = y := by
                  dsimp only [x₂]; rw [readRegs_eq_val (by decide : rVal2 ≠ rPres2)]; rfl
                let x₃ : SState := ⟨x₂.regs, Function.update x₂.stacks tmp1 (y :: x0.stacks tmp1)⟩
                have e₃ : StructuredCalls.Eval (mkAtom (.push tmp1 rVal2)) 1 x₂ x₃ := by
                  have ht : x₂.stacks tmp1 = x0.stacks tmp1 := by
                    simp [x₂, x₁, Function.update_of_ne h2t1.symm, Function.update_of_ne h1t1.symm]
                  have ep := eval_push x₂ tmp1 rVal2
                  rw [hv2, ht] at ep
                  exact ep
                refine ⟨2, x₃, .ite_true hp2 e₃, by omega, rfl,
                  by simp [x₃, x₂, x₁, Function.update_of_ne h1t1, Function.update_of_ne h12],
                  by simp [x₃, x₂, Function.update_of_ne h2t1],
                  by simp [x₃],
                  by simp [x₃, x₂, x₁, Function.update_of_ne ht12.symm, Function.update_of_ne h2t2.symm,
                    Function.update_of_ne h1t2.symm, hzs],
                  fun k hk1 hk2 hkt1 hkt2 => by
                    simp [x₃, x₂, x₁, Function.update_of_ne hkt1, Function.update_of_ne hk2,
                      Function.update_of_ne hk1]⟩
          obtain ⟨n₃, x₃, e₃, hn₃, hx3r, hx3d, hx3s, hx3t1, hx3t2, hx3o⟩ := hpart
          have hva : x₃.regs rVal = xs.head?.getD false := by
            rw [hx3r]; dsimp only [x₂, x₁]
            rw [readRegs_eq_other (by decide) (by decide),
              readRegs_eq_val (by decide : rVal ≠ rPres), hxs]
          have hvb : x₃.regs rVal2 = ys.head?.getD false := by
            rw [hx3r]; dsimp only [x₂]
            rw [readRegs_eq_val (by decide : rVal2 ≠ rPres2)]
          have hvc : x₃.regs rCarry = c := by
            rw [hx3r]; dsimp only [x₂, x₁]
            rw [readRegs_eq_other (by decide) (by decide),
              readRegs_eq_other (by decide) (by decide), hc]
          let aBit := xs.head?.getD false
          let bBit := ys.head?.getD false
          let bitOut := xor (xor aBit bBit) c
          let bNext := (!aBit && (bBit || c)) || (bBit && c)
          let x₄ : SState := ⟨Function.update x₃.regs rBit (x₃.regs rVal ^^ x₃.regs rVal2), x₃.stacks⟩
          have e₄ := eval_bxor x₃ rBit rVal rVal2
          let x₅ : SState := ⟨Function.update x₄.regs rBit (x₄.regs rBit ^^ x₄.regs rCarry), x₄.stacks⟩
          have e₅ := eval_bxor x₄ rBit rBit rCarry
          let x₆ : SState := ⟨x₅.regs, Function.update x₅.stacks tmp2 (x₅.regs rBit :: x₅.stacks tmp2)⟩
          have e₆ := eval_push x₅ tmp2 rBit
          let x₇ : SState := ⟨Function.update x₆.regs rTmp1 (!(x₆.regs rVal)), x₆.stacks⟩
          have e₇ := eval_bnot x₆ rTmp1 rVal
          let x₈ : SState := ⟨Function.update x₇.regs rTmp2 (x₇.regs rVal2 || x₇.regs rCarry), x₇.stacks⟩
          have e₈ := eval_bor x₇ rTmp2 rVal2 rCarry
          let x₉ : SState := ⟨Function.update x₈.regs rTmp1 (x₈.regs rTmp1 && x₈.regs rTmp2), x₈.stacks⟩
          have e₉ := eval_band x₈ rTmp1 rTmp1 rTmp2
          let x₁₀ : SState := ⟨Function.update x₉.regs rTmp2 (x₉.regs rVal2 && x₉.regs rCarry), x₉.stacks⟩
          have e₁₀ := eval_band x₉ rTmp2 rVal2 rCarry
          let x₁₁ : SState := ⟨Function.update x₁₀.regs rCarry (x₁₀.regs rTmp1 || x₁₀.regs rTmp2), x₁₀.stacks⟩
          have e₁₁ := eval_bor x₁₀ rCarry rTmp1 rTmp2
          obtain ⟨x₁₂, e₁₂, hx12s, hx12l, _, _, hx12c, hreg12⟩ := peekOrCond_eval dst s x₁₁
          have hx_bit : x₅.regs rBit = bitOut := by
            simp only [x₅, x₄, Function.update, Fin.ext_iff]
            norm_num
            try rw [show (0 : Fin R) = rVal from rfl]
            try rw [show (2 : Fin R) = rVal2 from rfl]
            try rw [show (4 : Fin R) = rCarry from rfl]
            rw [hva, hvb, hvc]
            dsimp only [bitOut, aBit, bBit]
            cases xs.head?.getD false <;> cases ys.head?.getD false <;> cases c <;> rfl
          have hx_carry : x₁₁.regs rCarry = bNext := by
            simp only [x₁₁, x₁₀, x₉, x₈, x₇, x₆, x₅, x₄, Function.update, Fin.ext_iff]
            norm_num
            try rw [show (0 : Fin R) = rVal from rfl]
            try rw [show (2 : Fin R) = rVal2 from rfl]
            try rw [show (4 : Fin R) = rCarry from rfl]
            rw [hva, hvb, hvc]
          have hx12_dst : x₁₂.stacks dst = xs.tail := by
            rw [hx12s]; dsimp only [x₁₁, x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_of_ne h1t2, hx3d]
          have hx12_s : x₁₂.stacks s = ys.tail := by
            rw [hx12s]; dsimp only [x₁₁, x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_of_ne h2t2, hx3s]
          have hx12_t2 : x₁₂.stacks tmp2 = bitOut :: zs := by
            rw [hx12s]; dsimp only [x₁₁, x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_self, hx_bit, show x₅.stacks tmp2 = zs from hx3t2]
          have hd_drop : xs.tail.length + ys.tail.length + 1 ≤ xs.length + ys.length := by
            cases xs with
            | nil =>
                cases ys with
                | nil => exact (hdone ⟨rfl, rfl⟩).elim
                | cons _ _ => simp [List.length_cons]
            | cons _ _ =>
                cases ys <;> simp [List.length_cons] <;> omega
          have hmeas : xs.tail.length + ys.tail.length ≤ m := by omega
          have hxs_eq_z : ((BinaryArithmetic.toNat xs : ℕ) : ℤ) =
              (bitVal aBit : ℤ) + 2 * ((BinaryArithmetic.toNat xs.tail : ℕ) : ℤ) := by
            cases xs <;> simp [BinaryArithmetic.toNat, aBit] <;> ring
          have hys_eq_z : ((BinaryArithmetic.toNat ys : ℕ) : ℤ) =
              (bitVal bBit : ℤ) + 2 * ((BinaryArithmetic.toNat ys.tail : ℕ) : ℤ) := by
            cases ys <;> simp [BinaryArithmetic.toNat, bBit] <;> ring
          have hbit := sub_bit_step_id aBit bBit c
          change (bitVal aBit : ℤ) - (bitVal bBit : ℤ) - (bitVal c : ℤ) =
            (bitVal bitOut : ℤ) - 2 * (bitVal bNext : ℤ) at hbit
          have hbout_le : (bitVal bitOut : ℤ) ≤ 1 := by cases bitOut <;> decide
          have hge_z : (0 : ℤ) ≤ ((BinaryArithmetic.toNat xs : ℕ) : ℤ) -
              ((BinaryArithmetic.toNat ys : ℕ) : ℤ) - (bitVal c : ℤ) := by omega
          have hge_rewrite : ((BinaryArithmetic.toNat xs : ℕ) : ℤ) -
              ((BinaryArithmetic.toNat ys : ℕ) : ℤ) - (bitVal c : ℤ) =
              (bitVal bitOut : ℤ) + 2 * (((BinaryArithmetic.toNat xs.tail : ℕ) : ℤ) -
                ((BinaryArithmetic.toNat ys.tail : ℕ) : ℤ) - (bitVal bNext : ℤ)) := by
            rw [hxs_eq_z, hys_eq_z]; linarith
          have hsub_next : BinaryArithmetic.toNat ys.tail + bitVal bNext ≤ BinaryArithmetic.toNat xs.tail := by
            have : (0 : ℤ) ≤ ((BinaryArithmetic.toNat xs.tail : ℕ) : ℤ) -
                ((BinaryArithmetic.toNat ys.tail : ℕ) : ℤ) - (bitVal bNext : ℤ) := by
              omega
            omega
          have hbody : StructuredCalls.Eval (subInPlaceBody dst s tmp1 tmp2) (n₃ + 13) x0 x₁₂ := by
            have hstep_cnt : 1 + (1 + (n₃ + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 3)))))))))) = n₃ + 13 := by omega
            rw [← hstep_cnt]
            exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆
              (.seq e₇ (.seq e₈ (.seq e₉ (.seq e₁₀ (.seq e₁₁ e₁₂))))))))))
          obtain ⟨nt, fin, htail, hnt, hfd, hfs, hft1, ⟨zs', hft2, hzs_len, hzs_val⟩, hfo, hreg_tail⟩ :=
            ih xs.tail ys.tail (bitOut :: zs) bNext x₁₂ hx12_dst hx12_s hx12_t2
              (hx12c.trans hx_carry) hmeas
              (by rw [← hx12s, hx12_dst, hx12_s] at hx12l; exact hx12l)
              hsub_next
          have hsum_step :
              ((BinaryArithmetic.toNat (bitOut :: zs).reverse : ℕ) : ℤ) +
                (2 : ℤ) ^ (bitOut :: zs).length *
                  (((BinaryArithmetic.toNat xs.tail : ℕ) : ℤ) -
                    ((BinaryArithmetic.toNat ys.tail : ℕ) : ℤ) - (bitVal bNext : ℤ)) =
              ((BinaryArithmetic.toNat zs.reverse : ℕ) : ℤ) +
                (2 : ℤ) ^ zs.length *
                  (((BinaryArithmetic.toNat xs : ℕ) : ℤ) -
                    ((BinaryArithmetic.toNat ys : ℕ) : ℤ) - (bitVal c : ℤ)) := by
            simp only [List.reverse_cons, toNat_append, List.length_cons, List.length_reverse,
              BinaryArithmetic.toNat, mul_zero, add_zero]
            push_cast
            rw [pow_succ', hge_rewrite]
            ring
          have hzs_len' : zs'.length ≤ zs.length + xs.length + ys.length := by
            simp only [List.length_cons] at hzs_len
            omega
          refine ⟨n₃ + 13 + nt + 1, fin, .while_true hloop_t hbody htail, by omega, hfd, hfs, ?_,
            ⟨zs', hft2, hzs_len', by rw [hzs_val, hsum_step]⟩, ?_, ?_⟩
          · rw [hft1, hx12s]; dsimp only [x₁₁, x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_of_ne ht12, hx3t1]; cases ys <;> simp
          · intro k hk1 hk2 hkt1 hkt2
            rw [hfo k hk1 hk2 hkt1 hkt2, hx12s]; dsimp only [x₁₁, x₁₀, x₉, x₈, x₇, x₆]
            rw [Function.update_of_ne hkt2, hx3o k hk1 hk2 hkt1 hkt2]
          · have hreg_pre : RegPreserved x0 x₃ := by
              have hr1 := regPreserved_readRegs (a := x0) (v := rVal) (p := rPres)
                (x0.stacks dst).head? x₁.stacks (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide)
              have hr2 := regPreserved_readRegs (a := x₁) (v := rVal2) (p := rPres2)
                ys.head? x₂.stacks (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide)
              have hr3 : RegPreserved x₂ x₃ := by simp [RegPreserved, hx3r]
              exact regPreserved_trans hr1 (regPreserved_trans hr2 hr3)
            exact regPreserved_trans hreg_pre
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
              (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
                (regPreserved_trans hreg12 hreg_tail))))))))
  let a₁ : SState := ⟨Function.update a.regs rCarry false, a.stacks⟩
  have e₁ := eval_set a rCarry false
  obtain ⟨a₂, e₂, ha2s, ha2l, _, _, ha2c, hreg2⟩ := peekOrCond_eval dst s a₁
  obtain ⟨n₃, b₃, e₃, hn₃, h3d, h3s, h3t1, ⟨zs', h3t2, hzs_len, hzs_val⟩, h3o, hreg3⟩ :=
    loop_aux ((a.stacks dst).length + (a.stacks s).length) (a.stacks dst) (a.stacks s) [] false a₂
      (by rw [ha2s]) (by rw [ha2s]) (by rw [ha2s, ht2]) (by rw [ha2c]; simp [a₁])
      le_rfl ha2l
      (by simpa [bitVal_false, add_zero] using hle)
  obtain ⟨n₄, b₄, e₄, hn₄, h4t1, h4s, h4o, hreg4, _, _, _⟩ := revMove_eval h2t1.symm b₃
  have h4d : b₄.stacks dst = [] := (h4o dst h1t1 h12).trans h3d
  have h4t2 : b₄.stacks tmp2 = zs' := (h4o tmp2 ht12.symm h2t2.symm).trans h3t2
  obtain ⟨n₅, b₅, e₅, hn₅, h5t2, h5o, hreg5⟩ := popLeadingFalse_eval tmp2 b₄
  have h5d : b₅.stacks dst = [] := (h5o dst h1t2).trans h4d
  have h5s : b₅.stacks s = a.stacks s := by
    rw [h5o s h2t2, h4s, h3s, h3t1, ha2s, ht1]; simp
  have h5t1 : b₅.stacks tmp1 = [] := (h5o tmp1 ht12).trans h4t1
  obtain ⟨n₆, b₆, e₆, hn₆, h6t2, h6d, h6o, hreg6, _, _, _⟩ := revMove_eval h1t2.symm b₅
  refine ⟨1 + (3 + (n₃ + (n₄ + (n₅ + n₆)))), b₆,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, ?_, ?_, ?_, h6t2, ?_, ?_⟩
  · have ht1_len : (b₃.stacks tmp1).length = (a.stacks s).length := by
      rw [h3t1, ha2s, ht1, List.append_nil, List.length_reverse]
    have ht2_len : zs'.length ≤ (a.stacks dst).length + (a.stacks s).length := by
      simp only [List.length_nil, zero_add] at hzs_len
      exact hzs_len
    have hstrip_len : (stripLeadingFalse zs').length ≤ zs'.length := by
      have hsr := congrArg List.length (stripLeadingFalse_reverse_eq zs'.reverse)
      simp only [List.reverse_reverse, List.length_reverse] at hsr
      have hlt := toNat_lt_two_pow zs'.reverse
      rw [List.length_reverse] at hlt
      rw [hsr]; exact bits_length_le_of_lt hlt
    rw [h4t2] at hn₅
    rw [hn₄, hn₆, h5t2, h4t2, ht1_len]
    omega
  · rw [h6d, h5d, List.append_nil, h5t2, h4t2, ← List.reverse_reverse zs',
      stripLeadingFalse_reverse_eq, List.reverse_reverse]
    simp only [List.reverse_nil, BinaryArithmetic.toNat, List.length_nil, pow_zero, one_mul,
      bitVal_false, Nat.cast_zero, sub_zero, zero_add] at hzs_val
    have hnat : BinaryArithmetic.toNat zs'.reverse =
        BinaryArithmetic.toNat (a.stacks dst) - BinaryArithmetic.toNat (a.stacks s) := by
      omega
    rw [hnat]
  · rw [h6o s h2t2 h12.symm, h5s]
  · rw [h6o tmp1 ht12 h1t1.symm, h5t1]
  · intro k hkd hks hkt1 hkt2
    rw [h6o k hkt2 hkd, h5o k hkt2, h4o k hkt1 hks, h3o k hkd hks hkt1 hkt2, ha2s]
  · exact regPreserved_trans
      (regPreserved_update _ _ (by decide) (by decide) (by decide))
      (regPreserved_trans hreg2 (regPreserved_trans hreg3
        (regPreserved_trans hreg4 (regPreserved_trans hreg5 hreg6))))

/-- 12. Multiplication into `dst` (`s1, s2 < 18`; `dst < 18 ∨ dst = sTmp3`; `{18..26}` cleared). -/
def mulStepBody : SCmd :=
  mkSeqList [
    mkAtom (.pop sMulA rVal rPres),
    mkIte rVal (addInPlace sMulAcc sMulB sTmp1 sTmp2) mkSkip,
    mkAtom (.set rBit false),
    mkAtom (.push sMulB rBit),
    mkAtom (.peek sMulA rTmp1 rLoop)
  ]

def mulToCore (s1 s2 dst : Fin S) : SCmd :=
  mkSeqList [
    copyStack s1 sMulA sTmp1,
    copyStack s2 sMulB sTmp1,
    clearStack sMulAcc,
    mkAtom (.peek sMulA rTmp1 rLoop),
    mkWhile rLoop mulStepBody,
    clearStack sMulB,
    moveStack sMulAcc dst sTmp1
  ]

theorem mulToCore_eval {s1 s2 dst : Fin S}
    (hs1 : s1.val < 18) (hs2 : s2.val < 18) (hdst : dst.val < 18 ∨ dst = sTmp3)
    (a : SState) (hscr : RangeCleared 18 26 a.stacks) :
    ∃ n b, StructuredCalls.Eval (mulToCore s1 s2 dst) n a b ∧
      n ≤ 80 * ((a.stacks s1).length + 1) * ((a.stacks s1).length + (a.stacks s2).length + 1) +
          3 * (a.stacks dst).length + 80 ∧
      b.stacks dst = (BinaryArithmetic.toNat (a.stacks s1) * BinaryArithmetic.toNat (a.stacks s2)).bits ∧
      RangeCleared 18 26 b.stacks ∧
      (∀ k, k.val < 18 → k ≠ dst → b.stacks k = a.stacks k) ∧
      (dst ≠ sTmp3 → b.stacks sTmp3 = a.stacks sTmp3) ∧
      RegPreserved a b := by
  let len1 := (a.stacks s1).length
  let len2 := (a.stacks s2).length
  let P := BinaryArithmetic.toNat (a.stacks s1) * BinaryArithmetic.toNat (a.stacks s2)
  have hP_lt : P < 2 ^ (len1 + len2) := by
    rw [pow_add]
    exact Nat.mul_lt_mul'' (toNat_lt_two_pow (a.stacks s1)) (toNat_lt_two_pow (a.stacks s2))
  have loop_aux : ∀ xs x0,
      x0.stacks sMulA = xs → x0.stacks sTmp1 = [] → x0.stacks sTmp2 = [] →
      x0.regs rLoop = !xs.isEmpty →
      xs.length + (x0.stacks sMulB).length = len1 + len2 →
      x0.stacks sMulAcc = (BinaryArithmetic.toNat (x0.stacks sMulAcc)).bits →
      BinaryArithmetic.toNat (x0.stacks sMulAcc) +
        BinaryArithmetic.toNat xs * BinaryArithmetic.toNat (x0.stacks sMulB) = P →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop mulStepBody) n x0 b ∧
        n ≤ xs.length * (68 * (len1 + len2) + 59) + 1 ∧
        b.stacks sMulA = [] ∧ b.stacks sTmp1 = [] ∧ b.stacks sTmp2 = [] ∧
        b.stacks sMulAcc = P.bits ∧
        (b.stacks sMulB).length = len1 + len2 ∧
        (∀ k, k ≠ sMulA → k ≠ sMulB → k ≠ sMulAcc → k ≠ sTmp1 → k ≠ sTmp2 →
          b.stacks k = x0.stacks k) ∧
        RegPreserved x0 b := by
    intro xs
    induction xs with
    | nil =>
        intro x0 hxs ht1 ht2 hhl hlen hcanon hsum
        simp at hhl
        simp only [BinaryArithmetic.toNat, zero_mul, add_zero] at hsum
        have hacc : x0.stacks sMulAcc = P.bits := by rw [hcanon, hsum]
        refine ⟨1, x0, .while_false hhl, by omega, hxs, ht1, ht2, hacc, by simpa using hlen,
          fun _ _ _ _ _ _ => rfl, regPreserved_refl x0⟩
    | cons hd tl ih =>
        intro x0 hxs ht1 ht2 hhl hlen hcanon hsum
        simp only [List.isEmpty_cons, Bool.not_false] at hhl
        let x₁ : SState := ⟨BitProgram.readRegs x0.regs rVal rPres (x0.stacks sMulA).head?,
          Function.update x0.stacks sMulA tl⟩
        have e₁ : StructuredCalls.Eval (mkAtom (.pop sMulA rVal rPres)) 1 x0 x₁ := by
          simpa [x₁, hxs] using eval_pop x0 sMulA rVal rPres
        have hval : x₁.regs rVal = hd := by
          dsimp only [x₁]; rw [hxs, readRegs_eq_val (by decide : rVal ≠ rPres)]; rfl
        have hacc_lt : BinaryArithmetic.toNat (x0.stacks sMulAcc) < 2 ^ (len1 + len2) := by
          have : BinaryArithmetic.toNat (x0.stacks sMulAcc) ≤ P := by omega
          exact lt_of_le_of_lt this hP_lt
        have hacc_len : (x0.stacks sMulAcc).length ≤ len1 + len2 := by
          rw [hcanon]; exact bits_length_le_of_lt hacc_lt
        have hb_len : (x0.stacks sMulB).length ≤ len1 + len2 := by omega
        have hpart : ∃ n₂ x₂, StructuredCalls.Eval
            (mkIte rVal (addInPlace sMulAcc sMulB sTmp1 sTmp2) mkSkip) n₂ x₁ x₂ ∧
            n₂ ≤ 68 * (len1 + len2) + 53 ∧
            x₂.stacks sMulA = tl ∧ x₂.stacks sMulB = x0.stacks sMulB ∧
            x₂.stacks sTmp1 = [] ∧ x₂.stacks sTmp2 = [] ∧
            x₂.stacks sMulAcc =
              (BinaryArithmetic.toNat (x0.stacks sMulAcc) +
                if hd then BinaryArithmetic.toNat (x0.stacks sMulB) else 0).bits ∧
            (∀ k, k ≠ sMulA → k ≠ sMulB → k ≠ sMulAcc → k ≠ sTmp1 → k ≠ sTmp2 →
              x₂.stacks k = x0.stacks k) ∧
            RegPreserved x₁ x₂ := by
          cases hd with
          | false =>
              have hf : x₁.regs rVal = false := hval
              refine ⟨1, x₁, .ite_false hf (.base (.skip x₁)), by omega,
                by simp [x₁],
                by simp [x₁, Function.update_of_ne (by decide : sMulB ≠ sMulA)],
                by simp [x₁, Function.update_of_ne (by decide : sTmp1 ≠ sMulA), ht1],
                by simp [x₁, Function.update_of_ne (by decide : sTmp2 ≠ sMulA), ht2],
                by dsimp only [x₁]; rw [Function.update_of_ne (by decide : sMulAcc ≠ sMulA)]; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]; exact hcanon,
                fun k hkA _ _ _ _ => by simp [x₁, Function.update_of_ne hkA],
                regPreserved_refl x₁⟩
          | true =>
              have ht_val : x₁.regs rVal = true := hval
              obtain ⟨na, xa, ea, hna, ha_acc, ha_b, ha_t1, ha_t2, ha_o, hreg_a⟩ :=
                addInPlace_eval (dst := sMulAcc) (s := sMulB) (tmp1 := sTmp1) (tmp2 := sTmp2)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  x₁
                  (by simp [x₁, Function.update_of_ne (by decide : sTmp1 ≠ sMulA), ht1])
                  (by simp [x₁, Function.update_of_ne (by decide : sTmp2 ≠ sMulA), ht2])
              have hacc1 : x₁.stacks sMulAcc = x0.stacks sMulAcc := by
                simp [x₁, Function.update_of_ne (by decide : sMulAcc ≠ sMulA)]
              have hb1 : x₁.stacks sMulB = x0.stacks sMulB := by
                simp [x₁, Function.update_of_ne (by decide : sMulB ≠ sMulA)]
              have hna' : na ≤ 68 * (len1 + len2) + 52 := by
                rw [hacc1, hb1] at hna
                omega
              refine ⟨na + 1, xa, .ite_true ht_val ea, by omega,
                by rw [ha_o sMulA (by decide) (by decide) (by decide) (by decide)]; simp [x₁],
                by rw [ha_b, hb1], ha_t1, ha_t2,
                by simpa [hacc1, hb1] using ha_acc,
                fun k hkA hkB hkAcc hkt1 hkt2 => by
                  rw [ha_o k hkAcc hkB hkt1 hkt2]; simp [x₁, Function.update_of_ne hkA],
                hreg_a⟩
        obtain ⟨n₂, x₂, e₂, hn₂, hx2A, hx2B, hx2t1, hx2t2, hx2acc, hx2o, hreg2⟩ := hpart
        let x₃ : SState := ⟨Function.update x₂.regs rBit false, x₂.stacks⟩
        have e₃ := eval_set x₂ rBit false
        let x₄ : SState := ⟨x₃.regs, Function.update x₃.stacks sMulB (x₃.regs rBit :: x₃.stacks sMulB)⟩
        have e₄ : StructuredCalls.Eval (mkAtom (.push sMulB rBit)) 1 x₃ x₄ := eval_push x₃ sMulB rBit
        have hx4_b : x₄.stacks sMulB = false :: x0.stacks sMulB := by
          dsimp only [x₄, x₃]
          rw [Function.update_self, Function.update_self, hx2B]
        let x₅ : SState := ⟨BitProgram.readRegs x₄.regs rTmp1 rLoop (x₄.stacks sMulA).head?, x₄.stacks⟩
        have e₅ := eval_peek x₄ sMulA rTmp1 rLoop
        have hx5_a : x₅.stacks sMulA = tl := by
          simp [x₅, x₄, x₃, Function.update_of_ne (by decide : sMulA ≠ sMulB), hx2A]
        have hx5_loop : x₅.regs rLoop = !tl.isEmpty := by
          dsimp only [x₅]
          rw [readRegs_eq_pres, show x₄.stacks sMulA = tl from by
            simpa [x₅] using hx5_a]
          cases tl <;> rfl
        have hx5_len : tl.length + (x₅.stacks sMulB).length = len1 + len2 := by
          simp only [x₅, hx4_b, List.length_cons]; simp [List.length_cons] at hlen; omega
        have hx5_acc : x₅.stacks sMulAcc = (BinaryArithmetic.toNat (x₅.stacks sMulAcc)).bits := by
          have hs_acc : x₅.stacks sMulAcc = x₂.stacks sMulAcc := by
            simp [x₅, x₄, x₃, Function.update_of_ne (by decide : sMulAcc ≠ sMulB)]
          rw [hs_acc, hx2acc, toNat_bits]
        have hx5_sum : BinaryArithmetic.toNat (x₅.stacks sMulAcc) +
            BinaryArithmetic.toNat tl * BinaryArithmetic.toNat (x₅.stacks sMulB) = P := by
          have hs_acc : x₅.stacks sMulAcc = x₂.stacks sMulAcc := by
            simp [x₅, x₄, x₃, Function.update_of_ne (by decide : sMulAcc ≠ sMulB)]
          have hs_b : x₅.stacks sMulB = false :: x0.stacks sMulB := by simpa [x₅] using hx4_b
          rw [hs_acc, hx2acc, toNat_bits, hs_b]
          simp only [BinaryArithmetic.toNat, bitVal_false, zero_add] at hsum ⊢
          cases hd <;> simp at hsum ⊢ <;> linarith
        have hbody : StructuredCalls.Eval mulStepBody (1 + (n₂ + 3)) x0 x₅ := by
          have hstep : 1 + (n₂ + (1 + (1 + 1))) = 1 + (n₂ + 3) := by omega
          rw [← hstep]
          exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
        obtain ⟨nt, fin, htail, hnt, hfA, hft1, hft2, hfacc, hfblen, hfo, hreg_tail⟩ :=
          ih x₅ hx5_a (by simp [x₅, x₄, x₃, Function.update_of_ne (by decide : sTmp1 ≠ sMulB), hx2t1])
            (by simp [x₅, x₄, x₃, Function.update_of_ne (by decide : sTmp2 ≠ sMulB), hx2t2])
            hx5_loop hx5_len hx5_acc hx5_sum
        refine ⟨(1 + (n₂ + 3)) + nt + 1, fin, .while_true hhl hbody htail, ?_,
          hfA, hft1, hft2, hfacc, hfblen, ?_, ?_⟩
        · simp only [List.length_cons]
          have : 1 + (n₂ + 3) + 1 ≤ 68 * (len1 + len2) + 59 := by omega
          have hmul : (tl.length + 1) * (68 * (len1 + len2) + 59) =
              tl.length * (68 * (len1 + len2) + 59) + (68 * (len1 + len2) + 59) := by ring
          linarith only [hnt, this, hmul]
        · intro k hkA hkB hkAcc hkt1 hkt2
          rw [hfo k hkA hkB hkAcc hkt1 hkt2]
          simp [x₅, x₄, x₃, Function.update_of_ne hkB, hx2o k hkA hkB hkAcc hkt1 hkt2]
        · exact regPreserved_trans
            (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
            (regPreserved_trans hreg2
            (regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
            (regPreserved_trans
              (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              hreg_tail)))
  have hs1A : s1 ≠ sMulA := fin_ne_of_lt_ge 18 hs1 (by decide)
  have hs1t1 : s1 ≠ sTmp1 := fin_ne_of_lt_ge 18 hs1 (by decide)
  have hs2B : s2 ≠ sMulB := fin_ne_of_lt_ge 18 hs2 (by decide)
  have hs2t1 : s2 ≠ sTmp1 := fin_ne_of_lt_ge 18 hs2 (by decide)
  have hADst : sMulA ≠ dst := by rcases hdst with h | rfl; exact (fin_ne_of_lt_ge 18 h (by decide)).symm; decide
  have hBDst : sMulB ≠ dst := by rcases hdst with h | rfl; exact (fin_ne_of_lt_ge 18 h (by decide)).symm; decide
  have hAccDst : sMulAcc ≠ dst := by rcases hdst with h | rfl; exact (fin_ne_of_lt_ge 18 h (by decide)).symm; decide
  have hDstT1 : dst ≠ sTmp1 := by rcases hdst with h | rfl; exact fin_ne_of_lt_ge 18 h (by decide); decide
  have hDstT2 : dst ≠ sTmp2 := by rcases hdst with h | rfl; exact fin_ne_of_lt_ge 18 h (by decide); decide
  obtain ⟨n₁, b₁, e₁, hn₁, h1s1, h1A, h1t1, h1o, hreg1⟩ :=
    copyStack_eval hs1A hs1t1 (by decide : sMulA ≠ sTmp1) a (hscr sTmp1 (by decide) (by decide))
  have h1B : b₁.stacks sMulB = [] := (h1o sMulB (by decide) (by decide)).trans (hscr sMulB (by decide) (by decide))
  have h1Acc : b₁.stacks sMulAcc = [] := (h1o sMulAcc (by decide) (by decide)).trans (hscr sMulAcc (by decide) (by decide))
  have h1t2 : b₁.stacks sTmp2 = [] := (h1o sTmp2 (by decide) (by decide)).trans (hscr sTmp2 (by decide) (by decide))
  have h1s2 : b₁.stacks s2 = a.stacks s2 := h1o s2 (fin_ne_of_lt_ge 18 hs2 (by decide)) hs2t1
  obtain ⟨n₂, b₂, e₂, hn₂, h2s2, h2B, h2t1, h2o, hreg2⟩ := copyStack_eval hs2B hs2t1 (by decide) b₁ h1t1
  have h2A : b₂.stacks sMulA = a.stacks s1 := (h2o sMulA (by decide) (by decide)).trans h1A
  have h2Acc : b₂.stacks sMulAcc = [] := (h2o sMulAcc (by decide) (by decide)).trans h1Acc
  have h2t2 : b₂.stacks sTmp2 = [] := (h2o sTmp2 (by decide) (by decide)).trans h1t2
  obtain ⟨n₃, b₃, e₃, hn₃, h3Acc, h3o, hreg3⟩ := clearStack_eval sMulAcc b₂
  have h3A : b₃.stacks sMulA = a.stacks s1 := (h3o sMulA (by decide)).trans h2A
  have h3B : b₃.stacks sMulB = a.stacks s2 := (h3o sMulB (by decide)).trans (h2B.trans h1s2)
  have h3t1 : b₃.stacks sTmp1 = [] := (h3o sTmp1 (by decide)).trans h2t1
  have h3t2 : b₃.stacks sTmp2 = [] := (h3o sTmp2 (by decide)).trans h2t2
  let b₄ : SState := ⟨BitProgram.readRegs b₃.regs rTmp1 rLoop (b₃.stacks sMulA).head?, b₃.stacks⟩
  have e₄ := eval_peek b₃ sMulA rTmp1 rLoop
  have hb4_loop : b₄.regs rLoop = !(a.stacks s1).isEmpty := by
    simp only [b₄, readRegs_eq_pres, h3A]; cases a.stacks s1 <;> rfl
  obtain ⟨n₅, b₅, e₅, hn₅, h5A, h5t1, h5t2, h5Acc, h5Blen, h5o, hreg5⟩ :=
    loop_aux (a.stacks s1) b₄ h3A h3t1 h3t2 hb4_loop
      (by change (a.stacks s1).length + (b₃.stacks sMulB).length = _; rw [h3B])
      (by simp [b₄, h3Acc, BinaryArithmetic.toNat, Nat.zero_bits])
      (by simp [b₄, h3Acc, h3A, h3B, BinaryArithmetic.toNat]; rfl)
  obtain ⟨n₆, b₆, e₆, hn₆, h6B, h6o, hreg6⟩ := clearStack_eval sMulB b₅
  have h6Acc : b₆.stacks sMulAcc = P.bits := (h6o sMulAcc (by decide)).trans h5Acc
  have h6A : b₆.stacks sMulA = [] := (h6o sMulA (by decide)).trans h5A
  have h6t1 : b₆.stacks sTmp1 = [] := (h6o sTmp1 (by decide)).trans h5t1
  have h6t2 : b₆.stacks sTmp2 = [] := (h6o sTmp2 (by decide)).trans h5t2
  obtain ⟨n₇, b₇, e₇, hn₇, h7Acc, h7dst, h7t1, h7o, hreg7⟩ :=
    moveStack_eval hAccDst (by decide : sMulAcc ≠ sTmp1) hDstT1 b₆ h6t1
  have hb6_dst : b₆.stacks dst = a.stacks dst := by
    rw [h6o dst hBDst.symm, h5o dst hADst.symm hBDst.symm hAccDst.symm hDstT1 hDstT2,
      show b₄.stacks dst = b₃.stacks dst from rfl, h3o dst hAccDst.symm,
      h2o dst hBDst.symm hDstT1, h1o dst hADst.symm hDstT1]
  have hpres_out : ∀ k : Fin S, k.val < 18 ∨ k = sTmp3 → k ≠ dst → b₇.stacks k = a.stacks k := by
    intro k hk hkd
    have hkA : k ≠ sMulA := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 18 h (by decide); decide
    have hkB : k ≠ sMulB := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 18 h (by decide); decide
    have hkAcc : k ≠ sMulAcc := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 18 h (by decide); decide
    have hkt1 : k ≠ sTmp1 := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 18 h (by decide); decide
    have hkt2 : k ≠ sTmp2 := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 18 h (by decide); decide
    rw [h7o k hkAcc hkd hkt1, h6o k hkB, h5o k hkA hkB hkAcc hkt1 hkt2,
      show b₄.stacks k = b₃.stacks k from rfl, h3o k hkAcc, h2o k hkB hkt1, h1o k hkA hkt1]
  refine ⟨n₁ + (n₂ + (n₃ + (1 + (n₅ + (n₆ + n₇))))), b₇,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, ?_, ?_,
    fun k hk hkd => hpres_out k (Or.inl hk) hkd,
    fun hd3 => hpres_out sTmp3 (Or.inr rfl) hd3.symm, ?_⟩
  · have hmulA_len : (a.stacks sMulA).length = 0 := by rw [hscr sMulA (by decide) (by decide)]; rfl
    have hb1B_len : (b₁.stacks sMulB).length = 0 := by rw [h1B]; rfl
    have hb2Acc_len : (b₂.stacks sMulAcc).length = 0 := by rw [h2Acc]; rfl
    rw [hn₁, hn₂, hn₃, hn₆, hn₇, hmulA_len, hb1B_len, h1s2, hb2Acc_len, h6Acc, hb6_dst]
    have hP_len : P.bits.length ≤ len1 + len2 := bits_length_le_of_lt hP_lt
    have h5_bd : n₅ ≤ len1 * (68 * (len1 + len2) + 59) + 1 := hn₅
    have hmul_rhs : 80 * (len1 + 1) * (len1 + len2 + 1) =
        80 * (len1 * (len1 + len2)) + 160 * len1 + 80 * len2 + 80 := by ring
    have hmul_lhs : len1 * (68 * (len1 + len2) + 59) =
        68 * (len1 * (len1 + len2)) + 59 * len1 := by ring
    linarith only [h5Blen, hP_len, h5_bd, hmul_rhs, hmul_lhs, Nat.zero_le (len1 * (len1 + len2))]
  · rw [h7dst, h6Acc]
  · intro k hk1 hk2
    by_cases hkA : k = sMulA
    · subst hkA; rw [h7o _ (by decide) hADst (by decide), h6A]
    · by_cases hkB : k = sMulB
      · subst hkB; rw [h7o _ (by decide) hBDst (by decide), h6B]
      · by_cases hkAcc : k = sMulAcc
        · subst hkAcc; exact h7Acc
        · by_cases hkt1 : k = sTmp1
          · subst hkt1; exact h7t1
          · by_cases hkt2 : k = sTmp2
            · subst hkt2; rw [h7o _ (by decide) hDstT2.symm (by decide), h6t2]
            · have hkd : k ≠ dst := by
                rcases hdst with h | rfl
                · exact fin_ne_of_val_ne (by omega)
                · exact fin_ne_of_val_ne (by dsimp only [sTmp3]; omega)
              rw [h7o k hkAcc hkd hkt1, h6o k hkB, h5o k hkA hkB hkAcc hkt1 hkt2,
                show b₄.stacks k = b₃.stacks k from rfl, h3o k hkAcc, h2o k hkB hkt1, h1o k hkA hkt1]
              exact hscr k hk1 hk2
  · exact regPreserved_trans hreg1 (regPreserved_trans hreg2 (regPreserved_trans hreg3
      (regPreserved_trans (regPreserved_readRegs _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      (regPreserved_trans hreg5 (regPreserved_trans hreg6 hreg7)))))

/-- 13. Division/modulo (`sNum < 18 ∨ sNum = sTmp3`; `sDen < 18`; `0 < toNat sDen`; `{21..26}` cleared). -/
def divStepBody : SCmd :=
  mkSeqList [
    mkAtom (.pop sDivN rBit rPres),
    mkAtom (.push sDivR rBit),
    stripZeros sDivR sTmp1,
    cmpGE sDivR sDivD sTmp1 sTmp2,
    mkAtom (.push sDivQ rCmp),
    mkIte rCmp (subInPlace sDivR sDivD sTmp1 sTmp2) mkSkip,
    mkAtom (.peek sDivN rTmp1 rLoop)
  ]

def divModCore (sNum sDen : Fin S) : SCmd :=
  mkSeqList [
    copyStack sNum sDivD sTmp1,
    revMove sDivD sDivN,
    copyStack sDen sDivD sTmp1,
    mkAtom (.peek sDivN rTmp1 rLoop),
    mkWhile rLoop divStepBody,
    clearStack sDivD,
    stripZeros sDivQ sTmp1,
    stripZeros sDivR sTmp1
  ]

theorem divModCore_eval {sNum sDen : Fin S}
    (hnum : sNum.val < 18 ∨ sNum = sTmp3) (hden : sDen.val < 18)
    (a : SState) (hdpos : 0 < BinaryArithmetic.toNat (a.stacks sDen))
    (hscr : RangeCleared 21 26 a.stacks) :
    ∃ n b, StructuredCalls.Eval (divModCore sNum sDen) n a b ∧
      n ≤ 200 * ((a.stacks sNum).length + 1) * ((a.stacks sDen).length + 1) + 60 ∧
      b.stacks sDivQ = (BinaryArithmetic.toNat (a.stacks sNum) / BinaryArithmetic.toNat (a.stacks sDen)).bits ∧
      b.stacks sDivR = (BinaryArithmetic.toNat (a.stacks sNum) % BinaryArithmetic.toNat (a.stacks sDen)).bits ∧
      b.stacks sDivN = [] ∧ b.stacks sDivD = [] ∧ b.stacks sTmp1 = [] ∧ b.stacks sTmp2 = [] ∧
      (∀ k, k.val < 21 ∨ k = sTmp3 → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  let lenN := (a.stacks sNum).length
  let lenD := (a.stacks sDen).length
  let N_orig := BinaryArithmetic.toNat (a.stacks sNum)
  let d := BinaryArithmetic.toNat (a.stacks sDen)
  have hd_lt : d < 2 ^ lenD := toNat_lt_two_pow (a.stacks sDen)
  have loop_aux : ∀ ms qs rs x0,
      x0.stacks sDivN = ms → x0.stacks sDivQ = qs → x0.stacks sDivR = rs →
      x0.stacks sDivD = a.stacks sDen →
      x0.stacks sTmp1 = [] → x0.stacks sTmp2 = [] →
      x0.regs rLoop = !ms.isEmpty →
      BinaryArithmetic.toNat rs < d →
      rs = (BinaryArithmetic.toNat rs).bits →
      (BinaryArithmetic.toNat qs * d + BinaryArithmetic.toNat rs) * 2 ^ ms.length +
        BinaryArithmetic.toNat ms.reverse = N_orig →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop divStepBody) n x0 b ∧
        n ≤ ms.length * (135 * lenD + 153) + 1 ∧
        b.stacks sDivN = [] ∧ b.stacks sDivD = a.stacks sDen ∧
        b.stacks sTmp1 = [] ∧ b.stacks sTmp2 = [] ∧
        BinaryArithmetic.toNat (b.stacks sDivR) < d ∧
        b.stacks sDivR = (BinaryArithmetic.toNat (b.stacks sDivR)).bits ∧
        (b.stacks sDivQ).length ≤ qs.length + ms.length ∧
        BinaryArithmetic.toNat (b.stacks sDivQ) * d + BinaryArithmetic.toNat (b.stacks sDivR) = N_orig ∧
        (∀ k, k ≠ sDivN → k ≠ sDivD → k ≠ sDivQ → k ≠ sDivR → k ≠ sTmp1 → k ≠ sTmp2 →
          b.stacks k = x0.stacks k) ∧
        RegPreserved x0 b := by
    intro ms
    induction ms with
    | nil =>
        intro qs rs x0 hN hQ hR hD ht1 ht2 hhl hdr hRcan hinv
        simp at hhl
        simp only [List.length_nil, pow_zero, mul_one, List.reverse_nil,
          BinaryArithmetic.toNat, add_zero] at hinv
        refine ⟨1, x0, .while_false hhl, by omega, hN, hD, ht1, ht2,
          by rwa [hR], by rwa [hR], by simp [hQ], by rwa [hQ, hR],
          fun _ _ _ _ _ _ _ => rfl, regPreserved_refl x0⟩
    | cons hd tl ih =>
        intro qs rs x0 hN hQ hR hD ht1 ht2 hhl hdr hRcan hinv
        simp only [List.isEmpty_cons, Bool.not_false] at hhl
        let x₁ : SState := ⟨BitProgram.readRegs x0.regs rBit rPres (x0.stacks sDivN).head?,
          Function.update x0.stacks sDivN tl⟩
        have e₁ : StructuredCalls.Eval (mkAtom (.pop sDivN rBit rPres)) 1 x0 x₁ := by
          simpa [x₁, hN] using eval_pop x0 sDivN rBit rPres
        have hbit : x₁.regs rBit = hd := by
          dsimp only [x₁]; rw [hN, readRegs_eq_val (by decide : rBit ≠ rPres)]; rfl
        let x₂ : SState := ⟨x₁.regs, Function.update x₁.stacks sDivR (x₁.regs rBit :: x₁.stacks sDivR)⟩
        have e₂ : StructuredCalls.Eval (mkAtom (.push sDivR rBit)) 1 x₁ x₂ :=
          eval_push x₁ sDivR rBit
        have hx2_r : x₂.stacks sDivR = hd :: rs := by
          dsimp only [x₂]
          rw [Function.update_self, hbit]
          dsimp only [x₁]
          rw [Function.update_of_ne (by decide : sDivR ≠ sDivN), hR]
        have hrs_len : rs.length ≤ lenD := by
          rw [hRcan]; exact bits_length_le_of_lt (lt_trans hdr hd_lt)
        have h2t1 : x₂.stacks sTmp1 = [] := by
          simp [x₂, x₁, Function.update_of_ne (by decide : sTmp1 ≠ sDivR),
            Function.update_of_ne (by decide : sTmp1 ≠ sDivN), ht1]
        obtain ⟨n₃, x₃, e₃, hn₃, hx3R, hx3t1, hx3o, hreg3⟩ :=
          stripZeros_eval (by decide : sDivR ≠ sTmp1) x₂ h2t1
        have hx3_R_val : BinaryArithmetic.toNat (x₃.stacks sDivR) =
            bitVal hd + 2 * BinaryArithmetic.toNat rs := by
          rw [hx3R, toNat_bits, hx2_r]; simp [BinaryArithmetic.toNat]
        have hx3_R_lt2d : BinaryArithmetic.toNat (x₃.stacks sDivR) < 2 * d := by
          rw [hx3_R_val]; cases hd <;> simp <;> omega
        have hx3_R_len : (x₃.stacks sDivR).length ≤ lenD + 1 := by
          rw [hx3R]
          apply bits_length_le_of_lt
          rw [pow_succ']
          have hlt2d : BinaryArithmetic.toNat (x₂.stacks sDivR) < 2 * d := by
            rw [hx2_r]; simp [BinaryArithmetic.toNat]; cases hd <;> simp <;> omega
          omega
        have hx3_D : x₃.stacks sDivD = a.stacks sDen := by
          rw [hx3o sDivD (by decide) (by decide)]
          simp [x₂, x₁, Function.update_of_ne (by decide : sDivD ≠ sDivR),
            Function.update_of_ne (by decide : sDivD ≠ sDivN), hD]
        have hx3_t2 : x₃.stacks sTmp2 = [] := by
          rw [hx3o sTmp2 (by decide) (by decide)]
          simp [x₂, x₁, Function.update_of_ne (by decide : sTmp2 ≠ sDivR),
            Function.update_of_ne (by decide : sTmp2 ≠ sDivN), ht2]
        obtain ⟨n₄, x₄, e₄, hn₄, hx4s, hx4cmp, hreg4⟩ :=
          cmpGE_eval (by decide : sDivR ≠ sDivD) (by decide : sDivR ≠ sTmp1) (by decide : sDivR ≠ sTmp2)
            (by decide : sDivD ≠ sTmp1) (by decide : sDivD ≠ sTmp2) (by decide : sTmp1 ≠ sTmp2)
            x₃ hx3t1 hx3_t2
        let qbit := decide (d ≤ BinaryArithmetic.toNat (x₃.stacks sDivR))
        have hqbit : x₄.regs rCmp = qbit := by rw [hx4cmp, hx3_D]
        let x₅ : SState := ⟨x₄.regs, Function.update x₄.stacks sDivQ (x₄.regs rCmp :: x₄.stacks sDivQ)⟩
        have e₅ := eval_push x₄ sDivQ rCmp
        have hx5_R : x₅.stacks sDivR = x₃.stacks sDivR := by
          simp [x₅, Function.update_of_ne (by decide : sDivR ≠ sDivQ), hx4s]
        have hx5_D : x₅.stacks sDivD = a.stacks sDen := by
          simp [x₅, Function.update_of_ne (by decide : sDivD ≠ sDivQ), hx4s, hx3_D]
        have hx5_t1 : x₅.stacks sTmp1 = [] := by
          simp [x₅, Function.update_of_ne (by decide : sTmp1 ≠ sDivQ), hx4s, hx3t1]
        have hx5_t2 : x₅.stacks sTmp2 = [] := by
          simp [x₅, Function.update_of_ne (by decide : sTmp2 ≠ sDivQ), hx4s, hx3_t2]
        have hpart : ∃ n₆ x₆, StructuredCalls.Eval
            (mkIte rCmp (subInPlace sDivR sDivD sTmp1 sTmp2) mkSkip) n₆ x₅ x₆ ∧
            n₆ ≤ 68 * lenD + 87 ∧
            x₆.stacks sDivR = (BinaryArithmetic.toNat (x₃.stacks sDivR) -
              if qbit then d else 0).bits ∧
            BinaryArithmetic.toNat (x₆.stacks sDivR) < d ∧
            x₆.stacks sDivD = a.stacks sDen ∧
            x₆.stacks sTmp1 = [] ∧ x₆.stacks sTmp2 = [] ∧
            (∀ k, k ≠ sDivR → k ≠ sDivD → k ≠ sTmp1 → k ≠ sTmp2 → x₆.stacks k = x₅.stacks k) ∧
            RegPreserved x₅ x₆ := by
          cases hqb : qbit with
          | false =>
              have hlt : BinaryArithmetic.toNat (x₃.stacks sDivR) < d := by
                have hq' : decide (d ≤ BinaryArithmetic.toNat (x₃.stacks sDivR)) = false := hqb
                rw [decide_eq_false_iff_not] at hq'
                omega
              have hc : x₅.regs rCmp = false := by dsimp only [x₅]; rw [hqbit, hqb]
              refine ⟨1, x₅, .ite_false hc (.base (.skip x₅)), by omega,
                by simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, hx5_R, hx3R, toNat_bits],
                by rwa [hx5_R], hx5_D, hx5_t1, hx5_t2, fun _ _ _ _ _ => rfl, regPreserved_refl x₅⟩
          | true =>
              have hle : BinaryArithmetic.toNat (x₅.stacks sDivD) ≤
                  BinaryArithmetic.toNat (x₅.stacks sDivR) := by
                rw [hx5_D, hx5_R]
                exact of_decide_eq_true (by simpa [qbit] using hqb)
              have hc : x₅.regs rCmp = true := by dsimp only [x₅]; rw [hqbit, hqb]
              obtain ⟨ns, xs, es, hns, hsR, hsD, hst1, hst2, hso, hregs⟩ :=
                subInPlace_eval (dst := sDivR) (s := sDivD) (tmp1 := sTmp1) (tmp2 := sTmp2)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  x₅ hx5_t1 hx5_t2 hle
              rw [hx5_R, hx5_D] at hns hsR
              refine ⟨ns + 1, xs, .ite_true hc es, by omega,
                by simpa [hqb] using hsR,
                by rw [hsR, toNat_bits]; omega,
                by rw [hsD, hx5_D], hst1, hst2, hso, hregs⟩
        obtain ⟨n₆, x₆, e₆, hn₆, hx6R, hx6R_lt, hx6D, hx6t1, hx6t2, hx6o, hreg6⟩ := hpart
        let x₇ : SState := ⟨BitProgram.readRegs x₆.regs rTmp1 rLoop (x₆.stacks sDivN).head?, x₆.stacks⟩
        have e₇ := eval_peek x₆ sDivN rTmp1 rLoop
        have hkeep_N : x₆.stacks sDivN = tl := by
          rw [hx6o sDivN (by decide) (by decide) (by decide) (by decide)]
          simp [x₅, Function.update_of_ne (by decide : sDivN ≠ sDivQ), hx4s,
            hx3o sDivN (by decide) (by decide), x₂, x₁,
            Function.update_of_ne (by decide : sDivN ≠ sDivR)]
        have hkeep_Q : x₆.stacks sDivQ = qbit :: qs := by
          rw [hx6o sDivQ (by decide) (by decide) (by decide) (by decide)]
          simp [x₅, hqbit, hx4s, hx3o sDivQ (by decide) (by decide),
            x₂, x₁, Function.update_of_ne (by decide : sDivQ ≠ sDivR),
            Function.update_of_ne (by decide : sDivQ ≠ sDivN), hQ]
        have hx7_Rcan : x₇.stacks sDivR = (BinaryArithmetic.toNat (x₇.stacks sDivR)).bits := by
          change x₆.stacks sDivR = _
          rw [hx6R, toNat_bits]
        have hx7_inv : (BinaryArithmetic.toNat (x₇.stacks sDivQ) * d +
            BinaryArithmetic.toNat (x₇.stacks sDivR)) * 2 ^ tl.length +
            BinaryArithmetic.toNat tl.reverse = N_orig := by
          have hqr : BinaryArithmetic.toNat (x₇.stacks sDivQ) * d +
              BinaryArithmetic.toNat (x₇.stacks sDivR) =
              2 * (BinaryArithmetic.toNat qs * d + BinaryArithmetic.toNat rs) + bitVal hd := by
            change BinaryArithmetic.toNat (x₆.stacks sDivQ) * d + BinaryArithmetic.toNat (x₆.stacks sDivR) = _
            rw [hkeep_Q, hx6R, toNat_bits, hx3_R_val]
            cases hqb : qbit with
            | false =>
                simp [BinaryArithmetic.toNat, bitVal_false]; ring
            | true =>
                have hdle : d ≤ bitVal hd + 2 * BinaryArithmetic.toNat rs := by
                  rw [← hx3_R_val]
                  exact of_decide_eq_true (by simpa [qbit] using hqb)
                simp only [BinaryArithmetic.toNat, bitVal_true, ↓reduceIte]
                zify [hdle]
                ring
          rw [hqr]
          calc
            (2 * (BinaryArithmetic.toNat qs * d + BinaryArithmetic.toNat rs) + bitVal hd) * 2 ^ tl.length +
                BinaryArithmetic.toNat tl.reverse
                = (BinaryArithmetic.toNat qs * d + BinaryArithmetic.toNat rs) * (2 * 2 ^ tl.length) +
                  (BinaryArithmetic.toNat tl.reverse + 2 ^ tl.length * bitVal hd) := by ring
            _ = (BinaryArithmetic.toNat qs * d + BinaryArithmetic.toNat rs) * 2 ^ (hd :: tl).length +
                  BinaryArithmetic.toNat (hd :: tl).reverse := by
                simp [List.length_cons, List.reverse_cons, toNat_append, BinaryArithmetic.toNat, pow_succ']
            _ = N_orig := hinv
        have hbody : StructuredCalls.Eval divStepBody (1 + (1 + (n₃ + (n₄ + (1 + (n₆ + 1)))))) x0 x₇ :=
          .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
        have hx7_inv' : (BinaryArithmetic.toNat (qbit :: qs) * d +
            BinaryArithmetic.toNat (x₆.stacks sDivR)) * 2 ^ tl.length +
            BinaryArithmetic.toNat tl.reverse = N_orig := by
          rw [← hkeep_Q]; exact hx7_inv
        obtain ⟨nt, fin, htail, hnt, hfN, hfD, hft1, hft2, hfRlt, hfRcan, hfQlen, hfInv, hfo, hreg_tail⟩ :=
          ih (qbit :: qs) (x₆.stacks sDivR) x₇ hkeep_N hkeep_Q rfl hx6D hx6t1 hx6t2
            (by simp only [x₇, readRegs_eq_pres, hkeep_N]; cases tl <;> rfl)
            hx6R_lt hx7_Rcan hx7_inv'
        refine ⟨(1 + (1 + (n₃ + (n₄ + (1 + (n₆ + 1)))))) + nt + 1, fin, .while_true hhl hbody htail, ?_,
          hfN, hfD, hft1, hft2, hfRlt, hfRcan, ?_, hfInv, ?_, ?_⟩
        · simp only [List.length_cons]
          rw [hx3_D] at hn₄
          have hiter : 1 + (1 + (n₃ + (n₄ + (1 + (n₆ + 1))))) + 1 ≤ 135 * lenD + 153 := by
            have := hn₃; rw [hx2_r] at this; simp only [List.length_cons] at this
            omega
          have hmul : (tl.length + 1) * (135 * lenD + 153) =
              tl.length * (135 * lenD + 153) + (135 * lenD + 153) := by ring
          linarith only [hnt, hiter, hmul]
        · simp only [List.length_cons] at hfQlen ⊢; omega
        · intro k hkN hkD hkQ hkR hkt1 hkt2
          rw [hfo k hkN hkD hkQ hkR hkt1 hkt2]
          change x₆.stacks k = x0.stacks k
          rw [hx6o k hkR hkD hkt1 hkt2]
          simp [x₅, Function.update_of_ne hkQ, hx4s, hx3o k hkR hkt1,
            x₂, x₁, Function.update_of_ne hkR, Function.update_of_ne hkN]
        · exact regPreserved_trans
            (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
            (regPreserved_trans hreg3 (regPreserved_trans hreg4 (regPreserved_trans hreg6
              (regPreserved_trans
                (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
                hreg_tail))))
  have hNumD : sNum ≠ sDivD := by rcases hnum with h | rfl; exact fin_ne_of_lt_ge 21 (by omega) (by decide); decide
  have hNumT1 : sNum ≠ sTmp1 := by rcases hnum with h | rfl; exact fin_ne_of_lt_ge 21 (by omega) (by decide); decide
  have hDenD : sDen ≠ sDivD := fin_ne_of_lt_ge 21 (by omega) (by decide)
  have hDenT1 : sDen ≠ sTmp1 := fin_ne_of_lt_ge 21 (by omega) (by decide)
  obtain ⟨n₁, b₁, e₁, hn₁, h1num, h1D, h1t1, h1o, hreg1⟩ :=
    copyStack_eval hNumD hNumT1 (by decide : sDivD ≠ sTmp1) a (hscr sTmp1 (by decide) (by decide))
  obtain ⟨n₂, b₂, e₂, hn₂, h2D, h2N, h2o, hreg2, _, _, _⟩ := revMove_eval (by decide : sDivD ≠ sDivN) b₁
  have h2t1 : b₂.stacks sTmp1 = [] := (h2o sTmp1 (by decide) (by decide)).trans h1t1
  have h2den : b₂.stacks sDen = a.stacks sDen := by
    have h1den : b₁.stacks sDen = a.stacks sDen := h1o sDen hDenD hDenT1
    rw [h2o sDen hDenD (fin_ne_of_lt_ge 21 (by omega) (by decide)), h1den]
  obtain ⟨n₃, b₃, e₃, hn₃, h3den, h3D, h3t1, h3o, hreg3⟩ := copyStack_eval hDenD hDenT1 (by decide) b₂ h2t1
  have h3N : b₃.stacks sDivN = (a.stacks sNum).reverse := by
    rw [h3o sDivN (by decide) (by decide), h2N, h1D, h1o sDivN (by decide) (by decide),
      (hscr sDivN (by decide) (by decide)), List.append_nil]
  have h3Q : b₃.stacks sDivQ = [] := by
    rw [h3o sDivQ (by decide) (by decide), h2o sDivQ (by decide) (by decide),
      h1o sDivQ (by decide) (by decide), hscr sDivQ (by decide) (by decide)]
  have h3R : b₃.stacks sDivR = [] := by
    rw [h3o sDivR (by decide) (by decide), h2o sDivR (by decide) (by decide),
      h1o sDivR (by decide) (by decide), hscr sDivR (by decide) (by decide)]
  have h3t2 : b₃.stacks sTmp2 = [] := by
    rw [h3o sTmp2 (by decide) (by decide), h2o sTmp2 (by decide) (by decide),
      h1o sTmp2 (by decide) (by decide), hscr sTmp2 (by decide) (by decide)]
  let b₄ : SState := ⟨BitProgram.readRegs b₃.regs rTmp1 rLoop (b₃.stacks sDivN).head?, b₃.stacks⟩
  have e₄ := eval_peek b₃ sDivN rTmp1 rLoop
  obtain ⟨n₅, b₅, e₅, hn₅, h5N, h5D, h5t1, h5t2, h5Rlt, h5Rcan, h5Qlen, h5Inv, h5o, hreg5⟩ :=
    loop_aux (a.stacks sNum).reverse [] [] b₄ h3N h3Q h3R (h3D.trans h2den) h3t1 h3t2
      (by simp only [b₄, readRegs_eq_pres, h3N]; cases (a.stacks sNum).reverse <;> rfl)
      hdpos rfl
      (by dsimp only [N_orig]; simp [b₄, h3Q, h3R, BinaryArithmetic.toNat, toNat_bits])
  obtain ⟨n₆, b₆, e₆, hn₆, h6D, h6o, hreg6⟩ := clearStack_eval sDivD b₅
  have h6t1 : b₆.stacks sTmp1 = [] := (h6o sTmp1 (by decide)).trans h5t1
  have h6Q : b₆.stacks sDivQ = b₅.stacks sDivQ := h6o sDivQ (by decide)
  have h6R : b₆.stacks sDivR = b₅.stacks sDivR := h6o sDivR (by decide)
  obtain ⟨n₇, b₇, e₇, hn₇, h7Q, h7t1, h7o, hreg7⟩ := stripZeros_eval (by decide : sDivQ ≠ sTmp1) b₆ h6t1
  have h7R : b₇.stacks sDivR = b₅.stacks sDivR := (h7o sDivR (by decide) (by decide)).trans h6R
  obtain ⟨n₈, b₈, e₈, hn₈, h8R, h8t1, h8o, hreg8⟩ := stripZeros_eval (by decide : sDivR ≠ sTmp1) b₇ h7t1
  have hq_div : BinaryArithmetic.toNat (b₅.stacks sDivQ) = N_orig / d := by
    have : (BinaryArithmetic.toNat (b₅.stacks sDivQ) * d + BinaryArithmetic.toNat (b₅.stacks sDivR)) / d =
        BinaryArithmetic.toNat (b₅.stacks sDivQ) := by
      rw [add_comm, Nat.add_mul_div_right _ _ hdpos, Nat.div_eq_of_lt h5Rlt, zero_add]
    rw [← h5Inv, this]
  have hr_mod : BinaryArithmetic.toNat (b₅.stacks sDivR) = N_orig % d := by
    have : (BinaryArithmetic.toNat (b₅.stacks sDivQ) * d + BinaryArithmetic.toNat (b₅.stacks sDivR)) % d =
        BinaryArithmetic.toNat (b₅.stacks sDivR) := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h5Rlt]
    rw [← h5Inv, this]
  refine ⟨n₁ + (n₂ + (n₃ + (1 + (n₅ + (n₆ + (n₇ + n₈)))))), b₈,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))),
    ?_, ?_, ?_, ?_, ?_, h8t1, ?_, ?_, ?_⟩
  · have haD_len : (a.stacks sDivD).length = 0 := by rw [hscr sDivD (by decide) (by decide)]; rfl
    have hR_len : (b₅.stacks sDivR).length ≤ lenD := by
      rw [h5Rcan]; exact bits_length_le_of_lt (lt_trans h5Rlt hd_lt)
    have hQ_len : (b₅.stacks sDivQ).length ≤ lenN := by
      simpa [h3Q, List.length_reverse] using h5Qlen
    rw [hn₁, hn₂, hn₃, hn₆, haD_len, h1D, h2D, List.length_nil, h2den, h5D]
    rw [h6Q] at hn₇
    rw [h7R] at hn₈
    have h5_bd : n₅ ≤ lenN * (135 * lenD + 153) + 1 := by
      simpa [List.length_reverse] using hn₅
    have hmul_rhs : 200 * (lenN + 1) * (lenD + 1) =
        200 * (lenN * lenD) + 200 * lenN + 200 * lenD + 200 := by ring
    have hmul_lhs : lenN * (135 * lenD + 153) = 135 * (lenN * lenD) + 153 * lenN := by ring
    linarith only [hR_len, hQ_len, h5_bd, hn₇, hn₈, hmul_rhs, hmul_lhs, Nat.zero_le (lenN * lenD)]
  · rw [h8o sDivQ (by decide) (by decide), h7Q, h6Q, hq_div]
  · rw [h8R, h7R, hr_mod]
  · rw [h8o sDivN (by decide) (by decide), h7o sDivN (by decide) (by decide), h6o sDivN (by decide), h5N]
  · rw [h8o sDivD (by decide) (by decide), h7o sDivD (by decide) (by decide), h6D]
  · rw [h8o sTmp2 (by decide) (by decide), h7o sTmp2 (by decide) (by decide), h6o sTmp2 (by decide), h5t2]
  · intro k hk
    have hkn : k ≠ sDivN := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 21 h (by decide); decide
    have hkd : k ≠ sDivD := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 21 h (by decide); decide
    have hkq : k ≠ sDivQ := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 21 h (by decide); decide
    have hkr : k ≠ sDivR := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 21 h (by decide); decide
    have hkt1 : k ≠ sTmp1 := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 21 h (by decide); decide
    have hkt2 : k ≠ sTmp2 := by rcases hk with h | rfl; exact fin_ne_of_lt_ge 21 h (by decide); decide
    rw [h8o k hkr hkt1, h7o k hkq hkt1, h6o k hkd, h5o k hkn hkd hkq hkr hkt1 hkt2,
      show b₄.stacks k = b₃.stacks k from rfl, h3o k hkd hkt1, h2o k hkd hkn, h1o k hkd hkt1]
  · exact regPreserved_trans hreg1 (regPreserved_trans hreg2 (regPreserved_trans hreg3
      (regPreserved_trans (regPreserved_readRegs _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      (regPreserved_trans hreg5 (regPreserved_trans hreg6 (regPreserved_trans hreg7 hreg8))))))

/-- 14. Modular multiplication `dst := ((toNat s1 * toNat s2) % toNat sMod).bits` (`dst` may alias `s1`/`s2`). -/
def mulMod (s1 s2 sMod dst : Fin S) : SCmd :=
  mkSeqList [
    mulToCore s1 s2 sTmp3,
    divModCore sTmp3 sMod,
    clearStack sTmp3,
    clearStack sDivQ,
    moveStack sDivR dst sTmp1
  ]

theorem mulMod_eval {s1 s2 sMod dst : Fin S}
    (hs1 : s1.val < 18) (hs2 : s2.val < 18) (hsmod : sMod.val < 18) (hdst : dst.val < 18)
    (a : SState) (hmpos : 0 < BinaryArithmetic.toNat (a.stacks sMod))
    (hscr : RangeCleared 18 27 a.stacks) :
    ∃ n b, StructuredCalls.Eval (mulMod s1 s2 sMod dst) n a b ∧
      n ≤ 350 * ((a.stacks s1).length + (a.stacks s2).length + (a.stacks sMod).length + 1) ^ 2 +
          3 * (a.stacks dst).length + 200 ∧
      b.stacks dst =
        ((BinaryArithmetic.toNat (a.stacks s1) * BinaryArithmetic.toNat (a.stacks s2)) %
          BinaryArithmetic.toNat (a.stacks sMod)).bits ∧
      RangeCleared 18 27 b.stacks ∧
      (∀ k, k.val < 18 → k ≠ dst → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  let l1 := (a.stacks s1).length
  let l2 := (a.stacks s2).length
  let lMod := (a.stacks sMod).length
  let P := BinaryArithmetic.toNat (a.stacks s1) * BinaryArithmetic.toNat (a.stacks s2)
  let M := BinaryArithmetic.toNat (a.stacks sMod)
  have hP_lt : P < 2 ^ (l1 + l2) := by
    rw [pow_add]; exact Nat.mul_lt_mul'' (toNat_lt_two_pow _) (toNat_lt_two_pow _)
  have hP_len : P.bits.length ≤ l1 + l2 := bits_length_le_of_lt hP_lt
  have hM_lt : M < 2 ^ lMod := toNat_lt_two_pow (a.stacks sMod)
  obtain ⟨n₁, b₁, e₁, hn₁, h1tmp3, h1scr, h1keep, _, hreg1⟩ :=
    mulToCore_eval hs1 hs2 (Or.inr rfl) a (rangeCleared_mono hscr le_rfl (by decide))
  have hm_b1 : b₁.stacks sMod = a.stacks sMod := h1keep sMod hsmod (fin_ne_of_lt_ge 18 hsmod (by decide))
  have hdst_b1 : b₁.stacks dst = a.stacks dst := h1keep dst hdst (fin_ne_of_lt_ge 18 hdst (by decide))
  obtain ⟨n₂, b₂, e₂, hn₂, h2Q, h2R, h2N, h2D, h2t1, h2t2, h2keep, hreg2⟩ :=
    divModCore_eval (Or.inr rfl) hsmod b₁ (by rwa [hm_b1]) (rangeCleared_mono h1scr (by decide) le_rfl)
  have h2tmp3 : b₂.stacks sTmp3 = P.bits := (h2keep sTmp3 (Or.inr rfl)).trans h1tmp3
  have h2dst : b₂.stacks dst = a.stacks dst :=
    (h2keep dst (Or.inl (Nat.lt_trans hdst (by decide)))).trans hdst_b1
  obtain ⟨n₃, b₃, e₃, hn₃, h3tmp3, h3o, hreg3⟩ := clearStack_eval sTmp3 b₂
  have h3Q : b₃.stacks sDivQ = (P / M).bits := by rw [h3o sDivQ (by decide), h2Q, h1tmp3, hm_b1, toNat_bits]
  have h3R : b₃.stacks sDivR = (P % M).bits := by rw [h3o sDivR (by decide), h2R, h1tmp3, hm_b1, toNat_bits]
  have h3t1 : b₃.stacks sTmp1 = [] := (h3o sTmp1 (by decide)).trans h2t1
  have h3dst : b₃.stacks dst = a.stacks dst :=
    (h3o dst (fin_ne_of_lt_ge 18 hdst (by decide))).trans h2dst
  obtain ⟨n₄, b₄, e₄, hn₄, h4Q, h4o, hreg4⟩ := clearStack_eval sDivQ b₃
  have h4R : b₄.stacks sDivR = (P % M).bits := (h4o sDivR (by decide)).trans h3R
  have h4t1 : b₄.stacks sTmp1 = [] := (h4o sTmp1 (by decide)).trans h3t1
  have h4dst : b₄.stacks dst = a.stacks dst :=
    (h4o dst (fin_ne_of_lt_ge 18 hdst (by decide))).trans h3dst
  obtain ⟨n₅, b₅, e₅, hn₅, h5R, h5dst, h5t1, h5o, hreg5⟩ :=
    moveStack_eval (fin_ne_of_lt_ge 18 hdst (by decide)).symm (by decide : sDivR ≠ sTmp1)
      (fin_ne_of_lt_ge 18 hdst (by decide)) b₄ h4t1
  refine ⟨n₁ + (n₂ + (n₃ + (n₄ + n₅))), b₅,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ?_, ?_, ?_, ?_⟩
  · have hQ_len : (P / M).bits.length ≤ l1 + l2 :=
      bits_length_le_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hP_lt)
    have hR_len : (P % M).bits.length ≤ lMod :=
      bits_length_le_of_lt (lt_trans (Nat.mod_lt _ hmpos) hM_lt)
    have htmp3_len : (a.stacks sTmp3).length = 0 := by rw [hscr sTmp3 (by decide) (by decide)]; rfl
    rw [htmp3_len] at hn₁
    rw [h1tmp3, hm_b1] at hn₂
    rw [h2tmp3] at hn₃
    rw [h3o sDivQ (by decide), h2Q, h1tmp3, hm_b1, toNat_bits] at hn₄
    rw [h4R, h4dst] at hn₅
    have hn₁' : n₁ ≤ 80 * (l1 + 1) * (l1 + l2 + 1) + 80 := hn₁
    have hn₂' : n₂ ≤ 200 * (l1 + l2 + 1) * (lMod + 1) + 60 := by
      have hmul : (P.bits.length + 1) * (lMod + 1) ≤ (l1 + l2 + 1) * (lMod + 1) :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_right hP_len 1)
      have h200 := Nat.mul_le_mul_left 200 hmul
      rw [Nat.mul_assoc] at hn₂ ⊢
      linarith only [hn₂, h200]
    have hsq : (l1 + 1) * (l1 + l2 + 1) ≤ (l1 + l2 + lMod + 1) ^ 2 ∧
        (l1 + l2 + 1) * (lMod + 1) ≤ (l1 + l2 + lMod + 1) ^ 2 := by
      constructor
      · rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
      · rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    have hlin_sq : l1 + l2 + lMod + 1 ≤ (l1 + l2 + lMod + 1) ^ 2 := by
      rw [sq]; exact Nat.le_mul_self _
    rw [Nat.mul_assoc] at hn₁' hn₂'
    linarith only [hn₁', hn₂', hn₃, hn₄, hn₅, hP_len, hQ_len, hR_len, hsq.1, hsq.2, hlin_sq]
  · rw [h5dst, h4R]
  · intro k hk1 hk2
    have hkd : k ≠ dst := (fin_ne_of_lt_ge 18 hdst hk1).symm
    by_cases hkA : k = sMulA
    · subst hkA; rw [h5o _ (by decide) hkd (by decide), h4o _ (by decide), h3o _ (by decide),
        h2keep _ (Or.inl (by decide)), h1scr sMulA (by decide) (by decide)]
    · by_cases hkB : k = sMulB
      · subst hkB; rw [h5o _ (by decide) hkd (by decide), h4o _ (by decide), h3o _ (by decide),
          h2keep _ (Or.inl (by decide)), h1scr sMulB (by decide) (by decide)]
      · by_cases hkAcc : k = sMulAcc
        · subst hkAcc; rw [h5o _ (by decide) hkd (by decide), h4o _ (by decide), h3o _ (by decide),
            h2keep _ (Or.inl (by decide)), h1scr sMulAcc (by decide) (by decide)]
        · by_cases hkN : k = sDivN
          · subst hkN; rw [h5o _ (by decide) hkd (by decide), h4o _ (by decide), h3o _ (by decide), h2N]
          · by_cases hkD : k = sDivD
            · subst hkD; rw [h5o _ (by decide) hkd (by decide), h4o _ (by decide), h3o _ (by decide), h2D]
            · by_cases hkQ : k = sDivQ
              · subst hkQ; rw [h5o _ (by decide) hkd (by decide), h4Q]
              · by_cases hkR : k = sDivR
                · subst hkR; exact h5R
                · by_cases hkt1 : k = sTmp1
                  · subst hkt1; exact h5t1
                  · by_cases hkt2 : k = sTmp2
                    · subst hkt2; rw [h5o _ (by decide) hkd (by decide), h4o _ (by decide),
                        h3o _ (by decide), h2t2]
                    · have : k = sTmp3 := Fin.ext (by
                        have hv18 : k.val ≠ sMulA.val := fun h => hkA (Fin.ext h)
                        have hv19 : k.val ≠ sMulB.val := fun h => hkB (Fin.ext h)
                        have hv20 : k.val ≠ sMulAcc.val := fun h => hkAcc (Fin.ext h)
                        have hv21 : k.val ≠ sDivN.val := fun h => hkN (Fin.ext h)
                        have hv22 : k.val ≠ sDivD.val := fun h => hkD (Fin.ext h)
                        have hv23 : k.val ≠ sDivQ.val := fun h => hkQ (Fin.ext h)
                        have hv24 : k.val ≠ sDivR.val := fun h => hkR (Fin.ext h)
                        have hv25 : k.val ≠ sTmp1.val := fun h => hkt1 (Fin.ext h)
                        have hv26 : k.val ≠ sTmp2.val := fun h => hkt2 (Fin.ext h)
                        dsimp only [sMulA, sMulB, sMulAcc, sDivN, sDivD, sDivQ, sDivR, sTmp1, sTmp2, sTmp3] at *
                        omega)
                      subst this
                      rw [h5o _ (by decide) hkd (by decide), h4o _ (by decide), h3tmp3]
  · intro k hk hkd
    rw [h5o k (fin_ne_of_lt_ge 18 hk (by decide)) hkd (fin_ne_of_lt_ge 18 hk (by decide)),
      h4o k (fin_ne_of_lt_ge 18 hk (by decide)), h3o k (fin_ne_of_lt_ge 18 hk (by decide)),
      h2keep k (Or.inl (by omega)), h1keep k hk (fin_ne_of_lt_ge 18 hk (by decide))]
  · exact regPreserved_trans hreg1 (regPreserved_trans hreg2
      (regPreserved_trans hreg3 (regPreserved_trans hreg4 hreg5)))

/-- 15. Modular exponentiation `dst := (powMod (toNat sMod) (toNat sBase) (toNat sExp)).bits`. -/
def powStepBody (sMod : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.pop sPowExp rBit rPres),
    mkIte rBit (mulMod sPowAcc sPowBase sMod sPowAcc) mkSkip,
    mulMod sPowBase sPowBase sMod sPowBase,
    mkAtom (.peek sPowExp rTmp1 rLoop)
  ]

def powModCmd (sMod sBase sExp dst : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.set rBit true),
    mkAtom (.push sPowAcc rBit),
    copyStack sBase sPowBase sTmp1,
    copyStack sExp sPowExp sTmp1,
    mkAtom (.peek sPowExp rTmp1 rLoop),
    mkWhile rLoop (powStepBody sMod),
    clearStack sPowBase,
    moveStack sPowAcc dst sTmp1
  ]

theorem powModCmd_eval {sMod sBase sExp dst : Fin S}
    (hsmod : sMod.val < 15) (hsbase : sBase.val < 15) (hsexp : sExp.val < 15)
    (hdst : dst.val < 15 ∨ dst = sTmp3)
    (a : SState) (hp2 : 2 ≤ BinaryArithmetic.toNat (a.stacks sMod))
    (hscr : RangeCleared 15 27 a.stacks) :
    ∃ n b, StructuredCalls.Eval (powModCmd sMod sBase sExp dst) n a b ∧
      n ≤ 7000 * ((a.stacks sExp).length + 1) *
          ((a.stacks sBase).length + (a.stacks sMod).length + 1) ^ 2 +
          3 * (a.stacks dst).length + 600 ∧
      b.stacks dst = (powMod (BinaryArithmetic.toNat (a.stacks sMod))
        (BinaryArithmetic.toNat (a.stacks sBase))
        (BinaryArithmetic.toNat (a.stacks sExp))).bits ∧
      (∀ k : Fin S, 15 ≤ k.val → k ≠ dst → b.stacks k = []) ∧
      (∀ k : Fin S, k.val < 15 → k ≠ dst → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  let p := BinaryArithmetic.toNat (a.stacks sMod)
  let b₀ := BinaryArithmetic.toNat (a.stacks sBase)
  let e₀ := BinaryArithmetic.toNat (a.stacks sExp)
  let lenMod := (a.stacks sMod).length
  let lenBase := (a.stacks sBase).length
  have hp_pos : 0 < p := by omega
  have hp_lt : p < 2 ^ lenMod := toNat_lt_two_pow (a.stacks sMod)
  have hlenMod2 : 2 ≤ lenMod := by
    by_contra hlt
    have hle1 : lenMod ≤ 1 := by omega
    have h2 : 2 ^ lenMod ≤ 2 := Nat.pow_le_pow_right (by decide) hle1
    omega
  have loop_aux : ∀ exp x0,
      x0.stacks sPowExp = exp → x0.stacks sMod = a.stacks sMod →
      RangeCleared 18 27 x0.stacks → x0.regs rLoop = !exp.isEmpty →
      BinaryArithmetic.toNat (x0.stacks sPowAcc) < p →
      x0.stacks sPowAcc = (BinaryArithmetic.toNat (x0.stacks sPowAcc)).bits →
      (x0.stacks sPowBase).length ≤ lenBase + lenMod →
      (BinaryArithmetic.toNat (x0.stacks sPowAcc) *
        (BinaryArithmetic.toNat (x0.stacks sPowBase)) ^ BinaryArithmetic.toNat exp) % p =
        (b₀ ^ e₀) % p →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop (powStepBody sMod)) n x0 b ∧
        n ≤ exp.length * (6400 * (lenBase + lenMod + 1) ^ 2) + 1 ∧
        b.stacks sPowExp = [] ∧ RangeCleared 18 27 b.stacks ∧
        b.stacks sPowAcc = ((b₀ ^ e₀) % p).bits ∧
        (b.stacks sPowBase).length ≤ lenBase + lenMod ∧
        (∀ k, k ≠ sPowExp → k ≠ sPowAcc → k ≠ sPowBase → k.val < 18 → b.stacks k = x0.stacks k) ∧
        RegPreserved x0 b := by
    intro exp
    induction exp with
    | nil =>
        intro x0 hexp hm hscr0 hhl hacc_lt hacc_can _ hinv
        simp at hhl
        simp only [BinaryArithmetic.toNat, pow_zero, mul_one, Nat.mod_eq_of_lt hacc_lt] at hinv
        have hacc : x0.stacks sPowAcc = ((b₀ ^ e₀) % p).bits := by rw [hacc_can, hinv]
        refine ⟨1, x0, .while_false hhl, by omega, hexp, hscr0, hacc, ‹_›,
          fun _ _ _ _ _ => rfl, regPreserved_refl x0⟩
    | cons hd tl ih =>
        intro x0 hexp hm hscr0 hhl hacc_lt hacc_can hb_len hinv
        simp only [List.isEmpty_cons, Bool.not_false] at hhl
        let x₁ : SState := ⟨BitProgram.readRegs x0.regs rBit rPres (x0.stacks sPowExp).head?,
          Function.update x0.stacks sPowExp tl⟩
        have e₁ : StructuredCalls.Eval (mkAtom (.pop sPowExp rBit rPres)) 1 x0 x₁ := by
          simpa [x₁, hexp] using eval_pop x0 sPowExp rBit rPres
        have hbit : x₁.regs rBit = hd := by
          dsimp only [x₁]; rw [hexp, readRegs_eq_val (by decide : rBit ≠ rPres)]; rfl
        have hacc_len : (x0.stacks sPowAcc).length ≤ lenMod := by
          rw [hacc_can]; exact bits_length_le_of_lt (lt_trans hacc_lt hp_lt)
        have hm1 : x₁.stacks sMod = a.stacks sMod := by
          dsimp only [x₁]
          rw [Function.update_of_ne (fin_ne_of_lt_ge 15 hsmod (by decide : 15 ≤ sPowExp.val)), hm]
        have hscr1 : RangeCleared 18 27 x₁.stacks := fun k hk1 hk2 => by
          dsimp only [x₁]
          rw [Function.update_of_ne (fin_ne_of_lt_ge 18 (by decide) hk1).symm]
          exact hscr0 k hk1 hk2
        have hacc1 : x₁.stacks sPowAcc = x0.stacks sPowAcc := by
          simp [x₁, Function.update_of_ne (by decide : sPowAcc ≠ sPowExp)]
        have hb1 : x₁.stacks sPowBase = x0.stacks sPowBase := by
          simp [x₁, Function.update_of_ne (by decide : sPowBase ≠ sPowExp)]
        have hpart : ∃ n₂ x₂, StructuredCalls.Eval
            (mkIte rBit (mulMod sPowAcc sPowBase sMod sPowAcc) mkSkip) n₂ x₁ x₂ ∧
            n₂ ≤ 3150 * (lenBase + lenMod + 1) ^ 2 + 3 * lenMod + 201 ∧
            x₂.stacks sPowAcc = (if hd then
              (BinaryArithmetic.toNat (x0.stacks sPowAcc) * BinaryArithmetic.toNat (x0.stacks sPowBase)) % p
              else BinaryArithmetic.toNat (x0.stacks sPowAcc)).bits ∧
            BinaryArithmetic.toNat (x₂.stacks sPowAcc) < p ∧
            RangeCleared 18 27 x₂.stacks ∧
            (∀ k, k.val < 18 → k ≠ sPowAcc → x₂.stacks k = x₁.stacks k) ∧
            RegPreserved x₁ x₂ := by
          cases hd with
          | false =>
              have hf : x₁.regs rBit = false := hbit
              refine ⟨1, x₁, .ite_false hf (.base (.skip x₁)), by omega, ?_,
                by rwa [hacc1], hscr1, fun _ _ _ => rfl, regPreserved_refl x₁⟩
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [hacc1]
              exact hacc_can
          | true =>
              have ht : x₁.regs rBit = true := hbit
              obtain ⟨nm, xm, em, hnm, hm_acc, hm_scr, hm_keep, hregm⟩ :=
                mulMod_eval (s1 := sPowAcc) (s2 := sPowBase) (sMod := sMod) (dst := sPowAcc)
                  (by decide) (by decide) (by omega) (by decide) x₁ (by rwa [hm1]) hscr1
              rw [hacc1, hb1, hm1] at hnm hm_acc
              have hle_m : nm ≤ 3150 * (lenBase + lenMod + 1) ^ 2 + 3 * lenMod + 200 := by
                have h3 : (x0.stacks sPowAcc).length + (x0.stacks sPowBase).length +
                    (a.stacks sMod).length + 1 ≤ 3 * (lenBase + lenMod + 1) := by omega
                have hsq : ((x0.stacks sPowAcc).length + (x0.stacks sPowBase).length +
                    (a.stacks sMod).length + 1) ^ 2 ≤ 9 * (lenBase + lenMod + 1) ^ 2 := by
                  have hp := Nat.pow_le_pow_left h3 2
                  have heq : (3 * (lenBase + lenMod + 1)) ^ 2 = 9 * (lenBase + lenMod + 1) ^ 2 := by ring
                  exact hp.trans_eq heq
                linarith only [hnm, hacc_len, hsq]
              refine ⟨nm + 1, xm, .ite_true ht em, by omega, by simpa using hm_acc,
                by rw [hm_acc, toNat_bits]; exact Nat.mod_lt _ hp_pos,
                hm_scr, hm_keep, hregm⟩
        obtain ⟨n₂, x₂, e₂, hn₂, hx2_acc, hx2_acclt, hx2_scr, hx2_keep, hreg2⟩ := hpart
        have hx2_mod : x₂.stacks sMod = a.stacks sMod := by
          rw [hx2_keep sMod (by omega) (fin_ne_of_lt_ge 15 hsmod (by decide)), hm1]
        have hx2_base : x₂.stacks sPowBase = x0.stacks sPowBase := by
          rw [hx2_keep sPowBase (by decide) (by decide), hb1]
        have hx2_exp : x₂.stacks sPowExp = tl := by
          rw [hx2_keep sPowExp (by decide) (by decide)]; simp [x₁]
        obtain ⟨n₃, x₃, e₃, hn₃, hx3_base, hx3_scr, hx3_keep, hreg3⟩ :=
          mulMod_eval (s1 := sPowBase) (s2 := sPowBase) (sMod := sMod) (dst := sPowBase)
            (by decide) (by decide) (by omega) (by decide) x₂ (by rwa [hx2_mod]) hx2_scr
        have hx3_exp : x₃.stacks sPowExp = tl := by
          rw [hx3_keep sPowExp (by decide) (by decide), hx2_exp]
        have hx3_mod : x₃.stacks sMod = a.stacks sMod := by
          rw [hx3_keep sMod (by omega) (fin_ne_of_lt_ge 15 hsmod (by decide)), hx2_mod]
        have hx3_acc : x₃.stacks sPowAcc = x₂.stacks sPowAcc :=
          hx3_keep sPowAcc (by decide) (by decide)
        let x₄ : SState := ⟨BitProgram.readRegs x₃.regs rTmp1 rLoop (x₃.stacks sPowExp).head?, x₃.stacks⟩
        have e₄ := eval_peek x₃ sPowExp rTmp1 rLoop
        have hx4_base_len : (x₄.stacks sPowBase).length ≤ lenBase + lenMod := by
          change (x₃.stacks sPowBase).length ≤ lenBase + lenMod
          rw [hx3_base, hx2_base, hx2_mod]
          exact le_trans (bits_length_le_of_lt (lt_trans (Nat.mod_lt _ hp_pos) hp_lt)) (by omega)
        have hx4_inv : (BinaryArithmetic.toNat (x₄.stacks sPowAcc) *
            (BinaryArithmetic.toNat (x₄.stacks sPowBase)) ^ BinaryArithmetic.toNat tl) % p =
            (b₀ ^ e₀) % p := by
          change (BinaryArithmetic.toNat (x₃.stacks sPowAcc) *
              (BinaryArithmetic.toNat (x₃.stacks sPowBase)) ^ BinaryArithmetic.toNat tl) % p = _
          rw [hx3_acc, hx2_acc, hx3_base, hx2_base, hx2_mod, toNat_bits, toNat_bits]
          have hstep := powMod_acc_step p (BinaryArithmetic.toNat (x0.stacks sPowAcc))
            (BinaryArithmetic.toNat (x0.stacks sPowBase)) hd tl
          cases hd with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hstep ⊢
              rw [← hstep, ← hinv]
              simp only [BinaryArithmetic.toNat, bitVal_false, zero_add]
              rw [← sq, ← pow_mul, pow_mul]
          | true =>
              simp only [↓reduceIte] at hstep ⊢
              rw [← hstep, ← hinv]
              simp only [BinaryArithmetic.toNat, bitVal_true]
              rw [show 1 + 2 * BinaryArithmetic.toNat tl = 2 * BinaryArithmetic.toNat tl + 1 from by omega,
                pow_succ', ← sq, ← pow_mul]
        have hbody : StructuredCalls.Eval (powStepBody sMod) (1 + (n₂ + (n₃ + 1))) x0 x₄ :=
          .seq e₁ (.seq e₂ (.seq e₃ e₄))
        obtain ⟨nt, fin, htail, hnt, hfexp, hfscr, hfacc, hfblen, hfo, hreg_tail⟩ :=
          ih x₄ hx3_exp hx3_mod hx3_scr
            (by simp only [x₄, readRegs_eq_pres, hx3_exp]; cases tl <;> rfl)
            (by rwa [show x₄.stacks sPowAcc = x₂.stacks sPowAcc from hx3_acc])
            (by change x₃.stacks sPowAcc = _; rw [hx3_acc, hx2_acc, toNat_bits])
            hx4_base_len hx4_inv
        refine ⟨(1 + (n₂ + (n₃ + 1))) + nt + 1, fin, .while_true hhl hbody htail, ?_,
          hfexp, hfscr, hfacc, hfblen, ?_, ?_⟩
        · simp only [List.length_cons]
          have h3_bd : n₃ ≤ 3150 * (lenBase + lenMod + 1) ^ 2 + 3 * (lenBase + lenMod) + 200 := by
            rw [hx2_base, hx2_mod] at hn₃
            have h3 : (x0.stacks sPowBase).length + (x0.stacks sPowBase).length +
                lenMod + 1 ≤ 3 * (lenBase + lenMod + 1) := by omega
            have hsq : ((x0.stacks sPowBase).length + (x0.stacks sPowBase).length +
                lenMod + 1) ^ 2 ≤ 9 * (lenBase + lenMod + 1) ^ 2 := by
              have hp := Nat.pow_le_pow_left h3 2
              have heq : (3 * (lenBase + lenMod + 1)) ^ 2 = 9 * (lenBase + lenMod + 1) ^ 2 := by ring
              exact hp.trans_eq heq
            linarith only [hn₃, hb_len, hsq]
          have hL3 : 3 ≤ lenBase + lenMod + 1 := by omega
          have hL_sq : lenBase + lenMod + 1 ≤ (lenBase + lenMod + 1) ^ 2 := by
            rw [sq]; exact Nat.le_mul_self _
          have hQ9 : 9 ≤ (lenBase + lenMod + 1) ^ 2 := by
            calc 9 = 3 ^ 2 := by norm_num
              _ ≤ (lenBase + lenMod + 1) ^ 2 := Nat.pow_le_pow_left hL3 2
          have hlin_q : 6 * lenBase + 9 * lenMod + 410 ≤ 100 * (lenBase + lenMod + 1) ^ 2 := by
            linarith only [hL_sq, hQ9]
          have hiter : 1 + (n₂ + (n₃ + 1)) + 1 ≤ 6400 * (lenBase + lenMod + 1) ^ 2 := by
            omega
          rw [Nat.add_mul, one_mul]
          omega
        · intro k hkExp hkAcc hkBase hk18
          rw [hfo k hkExp hkAcc hkBase hk18]
          change x₃.stacks k = x0.stacks k
          rw [hx3_keep k hk18 hkBase, hx2_keep k hk18 hkAcc]
          simp [x₁, Function.update_of_ne hkExp]
        · exact regPreserved_trans
            (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
            (regPreserved_trans hreg2 (regPreserved_trans hreg3
              (regPreserved_trans
                (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
                hreg_tail)))
  let a₁ : SState := ⟨Function.update a.regs rBit true, a.stacks⟩
  have e₁ := eval_set a rBit true
  let a₂ : SState := ⟨a₁.regs, Function.update a₁.stacks sPowAcc (true :: a₁.stacks sPowAcc)⟩
  have e₂ : StructuredCalls.Eval (mkAtom (.push sPowAcc rBit)) 1 a₁ a₂ := by
    simpa [a₂, a₁] using eval_push a₁ sPowAcc rBit
  have hsBase_B : sBase ≠ sPowBase := fin_ne_of_lt_ge 15 hsbase (by decide)
  have hsBase_T1 : sBase ≠ sTmp1 := fin_ne_of_lt_ge 15 hsbase (by decide)
  have hsExp_E : sExp ≠ sPowExp := fin_ne_of_lt_ge 15 hsexp (by decide)
  have hsExp_T1 : sExp ≠ sTmp1 := fin_ne_of_lt_ge 15 hsexp (by decide)
  have ha2_t1 : a₂.stacks sTmp1 = [] := by
    simp [a₂, a₁, Function.update_of_ne (by decide : sTmp1 ≠ sPowAcc), hscr sTmp1 (by decide) (by decide)]
  obtain ⟨n₃, b₃, e₃, hn₃, h3base_src, h3B, h3t1, h3o, hreg3⟩ :=
    copyStack_eval hsBase_B hsBase_T1 (by decide : sPowBase ≠ sTmp1) a₂ ha2_t1
  have h3exp_src : b₃.stacks sExp = a.stacks sExp := by
    rw [h3o sExp (fin_ne_of_lt_ge 15 hsexp (by decide)) hsExp_T1]
    have hExpAcc : sExp ≠ sPowAcc := fin_ne_of_lt_ge 15 hsexp (by decide)
    simp [a₂, a₁, Function.update_of_ne hExpAcc]
  obtain ⟨n₄, b₄, e₄, hn₄, h4exp_src, h4E, h4t1, h4o, hreg4⟩ :=
    copyStack_eval hsExp_E hsExp_T1 (by decide : sPowExp ≠ sTmp1) b₃ h3t1
  let b₅ : SState := ⟨BitProgram.readRegs b₄.regs rTmp1 rLoop (b₄.stacks sPowExp).head?, b₄.stacks⟩
  have e₅ := eval_peek b₄ sPowExp rTmp1 rLoop
  have h4mod : b₄.stacks sMod = a.stacks sMod := by
    rw [h4o sMod (fin_ne_of_lt_ge 15 hsmod (by decide)) (fin_ne_of_lt_ge 15 hsmod (by decide)),
      h3o sMod (fin_ne_of_lt_ge 15 hsmod (by decide)) (fin_ne_of_lt_ge 15 hsmod (by decide))]
    have hModAcc : sMod ≠ sPowAcc := fin_ne_of_lt_ge 15 hsmod (by decide)
    simp [a₂, a₁, Function.update_of_ne hModAcc]
  have h4acc : b₄.stacks sPowAcc = [true] := by
    rw [h4o sPowAcc (by decide) (by decide), h3o sPowAcc (by decide) (by decide)]
    simp [a₂, a₁, hscr sPowAcc (by decide) (by decide)]
  have h4base : b₄.stacks sPowBase = a.stacks sBase := by
    rw [h4o sPowBase (by decide) (by decide), h3B]
    have hBaseAcc : sBase ≠ sPowAcc := fin_ne_of_lt_ge 15 hsbase (by decide)
    simp [a₂, a₁, Function.update_of_ne hBaseAcc]
  have h4scr : RangeCleared 18 27 b₄.stacks := fun k hk1 hk2 => by
    by_cases hkt1 : k = sTmp1
    · subst hkt1; exact h4t1
    · have hkExp : k ≠ sPowExp := fin_ne_of_lt_ge 18 (by decide) hk1 |>.symm
      have hkBase : k ≠ sPowBase := fin_ne_of_lt_ge 18 (by decide) hk1 |>.symm
      have hkAcc : k ≠ sPowAcc := fin_ne_of_lt_ge 18 (by decide) hk1 |>.symm
      rw [h4o k hkExp hkt1, h3o k hkBase hkt1]
      dsimp only [a₂, a₁]
      rw [Function.update_of_ne hkAcc]
      exact hscr k (by omega) hk2
  obtain ⟨n₆, b₆, e₆, hn₆, h6E, h6scr, h6acc, h6blen, h6o, hreg6⟩ :=
    loop_aux (a.stacks sExp) b₅ (h4E.trans h3exp_src) h4mod h4scr
      (by dsimp only [b₅]; rw [readRegs_eq_pres, h4E.trans h3exp_src]; cases a.stacks sExp <;> rfl)
      (by change BinaryArithmetic.toNat (b₄.stacks sPowAcc) < p; rw [h4acc]; simp [BinaryArithmetic.toNat]; omega)
      (by change b₄.stacks sPowAcc = _; rw [h4acc]; rfl)
      (by change (b₄.stacks sPowBase).length ≤ _; rw [h4base]; omega)
      (by change (BinaryArithmetic.toNat (b₄.stacks sPowAcc) *
            (BinaryArithmetic.toNat (b₄.stacks sPowBase)) ^ BinaryArithmetic.toNat (a.stacks sExp)) % p = _
          dsimp only [b₀, e₀]; rw [h4acc, h4base]; simp [BinaryArithmetic.toNat])
  obtain ⟨n₇, b₇, e₇, hn₇, h7B, h7o, hreg7⟩ := clearStack_eval sPowBase b₆
  have h7t1 : b₇.stacks sTmp1 = [] := (h7o sTmp1 (by decide)).trans (h6scr sTmp1 (by decide) (by decide))
  have hAccDst : sPowAcc ≠ dst := by rcases hdst with h | rfl; exact (fin_ne_of_lt_ge 15 h (by decide)).symm; decide
  have hDstT1 : dst ≠ sTmp1 := by rcases hdst with h | rfl; exact fin_ne_of_lt_ge 15 h (by decide); decide
  obtain ⟨n₈, b₈, e₈, hn₈, h8acc, h8dst, h8t1, h8o, hreg8⟩ :=
    moveStack_eval hAccDst (by decide : sPowAcc ≠ sTmp1) hDstT1 b₇ h7t1
  have h7dst : b₇.stacks dst = a.stacks dst := by
    have h6dst : b₆.stacks dst = b₅.stacks dst := by
      rcases hdst with h | rfl
      · exact h6o dst (fin_ne_of_lt_ge 15 h (by decide)) (fin_ne_of_lt_ge 15 h (by decide))
          (fin_ne_of_lt_ge 15 h (by decide)) (by omega)
      · exact (h6scr sTmp3 (by decide) (by decide)).trans (h4scr sTmp3 (by decide) (by decide)).symm
    have hb4_dst : b₄.stacks dst = a.stacks dst := by
      rcases hdst with h | rfl
      · rw [h4o dst (fin_ne_of_lt_ge 15 h (by decide)) (fin_ne_of_lt_ge 15 h (by decide)),
          h3o dst (fin_ne_of_lt_ge 15 h (by decide)) (fin_ne_of_lt_ge 15 h (by decide))]
        have hAcc : dst ≠ sPowAcc := fin_ne_of_lt_ge 15 h (by decide)
        simp [a₂, a₁, Function.update_of_ne hAcc]
      · exact (h4scr sTmp3 (by decide) (by decide)).trans (hscr sTmp3 (by decide) (by decide)).symm
    rw [h7o dst (by rcases hdst with h | rfl; exact fin_ne_of_lt_ge 15 h (by decide : 15 ≤ sPowBase.val); decide),
      h6dst, show b₅.stacks dst = b₄.stacks dst from rfl, hb4_dst]
  refine ⟨1 + (1 + (n₃ + (n₄ + (1 + (n₆ + (n₇ + n₈)))))), b₈,
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))),
    ?_, ?_, ?_, ?_, ?_⟩
  · have haB_len : (a.stacks sPowBase).length = 0 := by rw [hscr sPowBase (by decide) (by decide)]; rfl
    have hb3E_len : (b₃.stacks sPowExp).length = 0 := by
      rw [h3o sPowExp (by decide) (by decide)]; simp [a₂, a₁, hscr sPowExp (by decide) (by decide)]
    have hacc_len : ((b₀ ^ e₀) % p).bits.length ≤ lenMod :=
      bits_length_le_of_lt (lt_trans (Nat.mod_lt _ hp_pos) hp_lt)
    rw [hn₃, hn₄, hn₇, hn₈, h7dst, h7o sPowAcc (by decide), h6acc]
    have ha2B : (a₂.stacks sPowBase).length = 0 := by simpa [a₂, a₁] using haB_len
    have ha3 : (a₂.stacks sBase).length = lenBase := by
      have hBaseAcc : sBase ≠ sPowAcc := fin_ne_of_lt_ge 15 hsbase (by decide)
      simp [a₂, a₁, Function.update_of_ne hBaseAcc]; rfl
    rw [ha2B, ha3, hb3E_len, h3exp_src]
    have hL3 : 3 ≤ lenBase + lenMod + 1 := by omega
    have hL_le : lenBase + lenMod + 1 ≤ (lenBase + lenMod + 1) ^ 2 := by
      rw [sq]; exact Nat.le_mul_self _
    have hQ9 : 9 ≤ (lenBase + lenMod + 1) ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ (lenBase + lenMod + 1) ^ 2 := Nat.pow_le_pow_left hL3 2
    have h_eQ : (a.stacks sExp).length * (6400 * (lenBase + lenMod + 1) ^ 2) + 9 * (a.stacks sExp).length ≤
        7000 * (a.stacks sExp).length * (lenBase + lenMod + 1) ^ 2 := by
      have h1 : 9 * (a.stacks sExp).length ≤ (a.stacks sExp).length * (600 * (lenBase + lenMod + 1) ^ 2) := by
        have h9 : 9 ≤ 600 * (lenBase + lenMod + 1) ^ 2 := by linarith only [hQ9]
        calc 9 * (a.stacks sExp).length = (a.stacks sExp).length * 9 := Nat.mul_comm _ _
          _ ≤ (a.stacks sExp).length * (600 * (lenBase + lenMod + 1) ^ 2) := Nat.mul_le_mul_left _ h9
      have h2 : (a.stacks sExp).length * (6400 * (lenBase + lenMod + 1) ^ 2) +
          (a.stacks sExp).length * (600 * (lenBase + lenMod + 1) ^ 2) =
          7000 * (a.stacks sExp).length * (lenBase + lenMod + 1) ^ 2 := by ring
      linarith only [h1, h2]
    have h_cQ : 12 * lenBase + 11 * lenMod + 25 ≤ 600 * (lenBase + lenMod + 1) ^ 2 + 590 := by
      linarith only [hL_le]
    have h_rhs : 7000 * ((a.stacks sExp).length + 1) * (lenBase + lenMod + 1) ^ 2 =
        7000 * (a.stacks sExp).length * (lenBase + lenMod + 1) ^ 2 + 7000 * (lenBase + lenMod + 1) ^ 2 := by ring
    linarith only [hn₆, h6blen, hacc_len, h_eQ, h_cQ, h_rhs, Nat.zero_le ((lenBase + lenMod + 1) ^ 2)]
  · rw [h8dst, h7o sPowAcc (by decide), h6acc, powMod_eq]
  · intro k hk15 hkd
    by_cases hkAcc : k = sPowAcc
    · subst hkAcc; exact h8acc
    · by_cases hkBase : k = sPowBase
      · subst hkBase; rw [h8o _ (by decide) hkd (by decide), h7B]
      · by_cases hkExp : k = sPowExp
        · subst hkExp; rw [h8o _ (by decide) hkd (by decide), h7o _ (by decide), h6E]
        · by_cases hkt1 : k = sTmp1
          · subst hkt1; exact h8t1
          · have hk18 : 18 ≤ k.val := by
              have hv15 : k.val ≠ sPowAcc.val := fun h => hkAcc (Fin.ext h)
              have hv16 : k.val ≠ sPowBase.val := fun h => hkBase (Fin.ext h)
              have hv17 : k.val ≠ sPowExp.val := fun h => hkExp (Fin.ext h)
              dsimp only [sPowAcc, sPowBase, sPowExp] at hv15 hv16 hv17
              omega
            rw [h8o k hkAcc hkd hkt1, h7o k hkBase, h6scr k hk18 (Nat.lt_succ_iff.mp k.isLt)]
  · intro k hk hkd
    have hkAcc : k ≠ sPowAcc := fin_ne_of_lt_ge 15 hk (by decide)
    have hkBase : k ≠ sPowBase := fin_ne_of_lt_ge 15 hk (by decide)
    have hkExp : k ≠ sPowExp := fin_ne_of_lt_ge 15 hk (by decide)
    have hkt1 : k ≠ sTmp1 := fin_ne_of_lt_ge 15 hk (by decide)
    rw [h8o k hkAcc hkd hkt1, h7o k hkBase, h6o k hkExp hkAcc hkBase (by omega),
      show b₅.stacks k = b₄.stacks k from rfl, h4o k hkExp hkt1, h3o k hkBase hkt1]
    simp [a₂, a₁, Function.update_of_ne hkAcc]
  · exact regPreserved_trans (regPreserved_update _ _ (by decide) (by decide) (by decide))
      (regPreserved_trans (regPreserved_refl _)
      (regPreserved_trans hreg3 (regPreserved_trans hreg4
      (regPreserved_trans (regPreserved_readRegs _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      (regPreserved_trans hreg6 (regPreserved_trans hreg7 hreg8))))))

end StackAndArith

/-! ## Section 4: Frame decoders, `unpackCmd`, `firstWitnessCmd`, `scanLoopCmd`, and `mainCmd` -/

section ScanKernel

theorem toNat_countWord (x : ℕ) : BinaryArithmetic.toNat (countWord x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [countWord, BinaryArithmetic.toNat]
  · simp [countWord, hx, toNat_bits]

theorem bits_ite_zero (x : ℕ) :
    (if x.bits.isEmpty then [false] else x.bits) = countWord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [countWord, Nat.zero_bits]
  · have hne : x.bits ≠ [] := by rw [ne_eq, bits_eq_nil_iff]; exact hx
    cases hb : x.bits with
    | nil => exact absurd hb hne
    | cons _ _ => simp [countWord, hx, hb]

theorem ioState_stackBits (word : List Bool) :
    BitProgram.stackBits (StructuredProgram.ioState (r := R) sIn word).stacks = word.length := by
  unfold BitProgram.stackBits
  rw [Finset.sum_eq_single_of_mem sIn (Finset.mem_univ sIn)]
  · simp [StructuredProgram.ioState]
  · intro k _ hk; dsimp [StructuredProgram.ioState]; split_ifs <;> simp_all

def frameTail : List Bool → List Bool
  | [] => []
  | b :: bs => b :: Encoding.frame bs

theorem frame_eq_tag_append_frameTail (w : List Bool) :
    Encoding.frame w = (!w.isEmpty) :: frameTail w := by
  cases w with
  | nil => rfl
  | cons _ _ => rfl

theorem frameTail_length (w : List Bool) : (frameTail w).length = 2 * w.length := by
  cases w with
  | nil => rfl
  | cons b bs => simp [frameTail, frame_length]; omega

def encNatPrefix : List ℕ → List Bool
  | [] => []
  | x :: xs => true :: Encoding.frame (countWord x) ++ encNatPrefix xs

theorem encNatPrefix_append (xs ys : List ℕ) :
    encNatPrefix (xs ++ ys) = encNatPrefix xs ++ encNatPrefix ys := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [encNatPrefix, ih, List.append_assoc]

theorem encodeNatListBin_eq_prefix_append (xs ys : List ℕ) :
    encodeNatListBin (xs ++ ys) = encNatPrefix xs ++ encodeNatListBin ys := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      change true :: (Encoding.frame (countWord a) ++ encodeNatListBin (rest ++ ys)) =
        (true :: Encoding.frame (countWord a) ++ encNatPrefix rest) ++ encodeNatListBin ys
      rw [ih]
      simp [List.cons_append, List.append_assoc]

theorem stackBits_pop_push_drop (stk : Fin S → List Bool) (src dst : Fin S) (hne : src ≠ dst)
    (a b : Bool) (xs : List Bool) (hs : stk src = a :: b :: xs) :
    BitProgram.stackBits (Function.update (Function.update stk src xs) dst (a :: stk dst)) + 1 =
      BitProgram.stackBits stk := by
  let stk1 := Function.update stk src xs
  have h1 := BitProgram.stackBits_update stk src xs
  have h2 := BitProgram.stackBits_update stk1 dst (a :: stk dst)
  have hdst1 : stk1 dst = stk dst := Function.update_of_ne hne.symm _ stk
  dsimp only [stk1] at h2 hdst1
  rw [hdst1] at h2
  simp only [List.length_cons, hs] at h1 h2
  omega

/-- 16. Frame decoder `popFrame`: pops `Encoding.frame w` from `src` onto `dst` via `tmp`. -/
def popFrameBody (src tmp : Fin S) : SCmd :=
  mkSeqList [mkAtom (.pop src rVal rPres), mkAtom (.push tmp rVal), mkAtom (.pop src rLoop rPres)]

def popFrame (src dst tmp : Fin S) : SCmd :=
  mkSeqList [mkAtom (.pop src rLoop rPres), mkWhile rLoop (popFrameBody src tmp), revMove tmp dst]

theorem popFrame_loop_eval {src tmp : Fin S} (hne : src ≠ tmp)
    (w tail : List Bool) (x0 : SState)
    (hsrc : x0.stacks src = frameTail w ++ tail)
    (hhl : x0.regs rLoop = !w.isEmpty) :
    ∃ n b, StructuredCalls.Eval (mkWhile rLoop (popFrameBody src tmp)) n x0 b ∧
      n = 4 * w.length + 1 ∧
      b.stacks src = tail ∧
      b.stacks tmp = w.reverse ++ x0.stacks tmp ∧
      (∀ k, k ≠ src → k ≠ tmp → b.stacks k = x0.stacks k) ∧
      RegPreserved x0 b ∧
      BitProgram.stackBits b.stacks + w.length = BitProgram.stackBits x0.stacks := by
  induction w generalizing x0 with
  | nil =>
      simp only [List.isEmpty_nil, Bool.not_true, frameTail, List.nil_append] at hhl hsrc ⊢
      exact ⟨1, x0, .while_false hhl, rfl, hsrc, by simp, fun _ _ _ => rfl,
        regPreserved_refl x0, by simp⟩
  | cons hd tl ih =>
      simp only [List.isEmpty_cons, Bool.not_false] at hhl
      rw [frameTail, frame_eq_tag_append_frameTail] at hsrc
      simp only [List.cons_append] at hsrc
      let x₁ : SState := ⟨BitProgram.readRegs x0.regs rVal rPres (some hd),
        Function.update x0.stacks src ((!tl.isEmpty) :: (frameTail tl ++ tail))⟩
      have e₁ : StructuredCalls.Eval (mkAtom (.pop src rVal rPres)) 1 x0 x₁ := by
        simpa [x₁, hsrc] using eval_pop x0 src rVal rPres
      have hv1 : x₁.regs rVal = hd := by
        dsimp only [x₁]; rw [readRegs_eq_val (by decide : rVal ≠ rPres)]; rfl
      let x₂ : SState := ⟨x₁.regs, Function.update x₁.stacks tmp (x₁.regs rVal :: x₁.stacks tmp)⟩
      have e₂ : StructuredCalls.Eval (mkAtom (.push tmp rVal)) 1 x₁ x₂ :=
        eval_push x₁ tmp rVal
      have hx2_src : x₂.stacks src = (!tl.isEmpty) :: (frameTail tl ++ tail) := by
        dsimp only [x₂, x₁]; rw [Function.update_of_ne hne, Function.update_self]
      let x₃ : SState := ⟨BitProgram.readRegs x₂.regs rLoop rPres (some (!tl.isEmpty)),
        Function.update x₂.stacks src (frameTail tl ++ tail)⟩
      have e₃ : StructuredCalls.Eval (mkAtom (.pop src rLoop rPres)) 1 x₂ x₃ := by
        simpa [x₃, hx2_src] using eval_pop x₂ src rLoop rPres
      have hx3_tmp : x₃.stacks tmp = hd :: x0.stacks tmp := by
        dsimp only [x₃, x₂, x₁]
        rw [Function.update_of_ne hne.symm, Function.update_self,
          Function.update_of_ne hne.symm, ← hv1]
        dsimp only [x₁]; rw [readRegs_eq_val (by decide : rVal ≠ rPres)]; rfl
      have hx3_loop : x₃.regs rLoop = !tl.isEmpty := by
        dsimp only [x₃]; rw [readRegs_eq_val (by decide : rLoop ≠ rPres)]; rfl
      have hx3_bits : BitProgram.stackBits x₃.stacks + 1 = BitProgram.stackBits x0.stacks := by
        have hstk : x₃.stacks = Function.update
            (Function.update x0.stacks src (frameTail tl ++ tail)) tmp (hd :: x0.stacks tmp) := by
          funext k
          by_cases hks : k = src
          · subst hks
            dsimp only [x₃]
            rw [Function.update_self, Function.update_of_ne hne, Function.update_self]
          · by_cases hkt : k = tmp
            · subst hkt; rw [hx3_tmp, Function.update_self]
            · dsimp only [x₃, x₂, x₁]
              rw [Function.update_of_ne hks, Function.update_of_ne hkt, Function.update_of_ne hks,
                Function.update_of_ne hkt, Function.update_of_ne hks]
        rw [hstk]
        exact stackBits_pop_push_drop x0.stacks src tmp hne hd (!tl.isEmpty) (frameTail tl ++ tail) hsrc
      have hx3_src : x₃.stacks src = frameTail tl ++ tail := by
        dsimp only [x₃]; rw [Function.update_self]
      obtain ⟨nt, fin, htail, hnt, hfs, hft, hfo, hreg_t, hbits_t⟩ :=
        ih x₃ hx3_src hx3_loop
      refine ⟨3 + nt + 1, fin, .while_true hhl (.seq e₁ (.seq e₂ e₃)) htail, ?_, hfs, ?_, ?_, ?_, ?_⟩
      · simp [List.length_cons, hnt]; omega
      · rw [hft, hx3_tmp]; simp [List.reverse_cons]
      · intro k hks hkt
        rw [hfo k hks hkt]
        dsimp only [x₃, x₂, x₁]
        rw [Function.update_of_ne hks, Function.update_of_ne hkt, Function.update_of_ne hks]
      · exact regPreserved_trans
          (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
          (regPreserved_trans
            (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
            hreg_t)
      · simp only [List.length_cons]; omega

theorem popFrame_spec {inS outS src dst tmp : Fin S}
    (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (w tail : List Bool) (a : SState)
    (hsrc : a.stacks src = Encoding.frame w ++ tail)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = [])
    {B : ℕ} (hB : BitProgram.stackBits a.stacks + 10 ≤ B) :
    ∃ n b, Spec inS outS (popFrame src dst tmp) a b n B ∧
      n = 8 * w.length + 4 ∧
      b.stacks src = tail ∧ b.stacks dst = w ∧ b.stacks tmp = [] ∧
      (∀ k, k ≠ src → k ≠ dst → k ≠ tmp → b.stacks k = a.stacks k) ∧
      RegPreserved a b ∧
      BitProgram.stackBits b.stacks + w.length + 1 = BitProgram.stackBits a.stacks := by
  have hsrc' : a.stacks src = (!w.isEmpty) :: (frameTail w ++ tail) := by
    rw [hsrc, frame_eq_tag_append_frameTail, List.cons_append]
  let a₁ : SState := ⟨BitProgram.readRegs a.regs rLoop rPres (some (!w.isEmpty)),
    Function.update a.stacks src (frameTail w ++ tail)⟩
  have e₁_ev : StructuredCalls.Eval (mkAtom (.pop src rLoop rPres)) 1 a a₁ := by
    simpa [a₁, hsrc'] using eval_pop a src rLoop rPres
  have sp₁ : Spec inS outS (mkAtom (.pop src rLoop rPres)) a a₁ 1 B :=
    Spec.of_eval_local e₁_ev (by omega)
  have ha1_loop : a₁.regs rLoop = !w.isEmpty := by
    dsimp only [a₁]; rw [readRegs_eq_val (by decide : rLoop ≠ rPres)]; rfl
  have ha1_src : a₁.stacks src = frameTail w ++ tail := by
    dsimp only [a₁]; rw [Function.update_self]
  have ha1_bits : BitProgram.stackBits a₁.stacks + 1 = BitProgram.stackBits a.stacks := by
    have hup := BitProgram.stackBits_update a.stacks src (frameTail w ++ tail)
    rw [hsrc'] at hup; simp only [List.length_cons] at hup
    dsimp only [a₁]; omega
  obtain ⟨nt, b₂, e₂_ev, hnt, h2src, h2tmp, h2o, h2reg, h2bits⟩ :=
    popFrame_loop_eval h2 w tail a₁ ha1_src ha1_loop
  let I : SState → Prop := fun x =>
    ∃ w_cur : List Bool,
      x.stacks src = frameTail w_cur ++ tail ∧
      x.regs rLoop = !w_cur.isEmpty ∧
      BitProgram.stackBits x.stacks ≤ BitProgram.stackBits a.stacks
  have hinit : ∀ x, I x → ∀ i, (x.stacks i).length ≤ B := by
    intro x ⟨_, _, _, hx⟩ i
    exact (stackLength_le_stackBits x.stacks i).trans (hx.trans (by omega))
  have hstep : ∀ x, I x → x.regs rLoop = true →
      ∃ m y, Spec inS outS (popFrameBody src tmp) x y m B ∧ I y := by
    intro x ⟨wc, hxsrc, hxloop, hxb⟩ hlt
    cases wc with
    | nil => simp at hxloop; rw [hxloop] at hlt; cases hlt
    | cons hd tl =>
        rw [frameTail, frame_eq_tag_append_frameTail] at hxsrc
        simp only [List.cons_append] at hxsrc
        let y₁ : SState := ⟨BitProgram.readRegs x.regs rVal rPres (some hd),
          Function.update x.stacks src ((!tl.isEmpty) :: (frameTail tl ++ tail))⟩
        have hy₁ : StructuredCalls.Eval (mkAtom (.pop src rVal rPres)) 1 x y₁ := by
          simpa [y₁, hxsrc] using eval_pop x src rVal rPres
        let y₂ : SState := ⟨y₁.regs, Function.update y₁.stacks tmp (y₁.regs rVal :: y₁.stacks tmp)⟩
        have hy₂ : StructuredCalls.Eval (mkAtom (.push tmp rVal)) 1 y₁ y₂ := eval_push y₁ tmp rVal
        have hy2_src : y₂.stacks src = (!tl.isEmpty) :: (frameTail tl ++ tail) := by
          dsimp only [y₂, y₁]; rw [Function.update_of_ne h2, Function.update_self]
        let y₃ : SState := ⟨BitProgram.readRegs y₂.regs rLoop rPres (some (!tl.isEmpty)),
          Function.update y₂.stacks src (frameTail tl ++ tail)⟩
        have hy₃ : StructuredCalls.Eval (mkAtom (.pop src rLoop rPres)) 1 y₂ y₃ := by
          simpa [y₃, hy2_src] using eval_pop y₂ src rLoop rPres
        have hv : y₁.regs rVal = hd := by
          dsimp only [y₁]; rw [readRegs_eq_val (by decide : rVal ≠ rPres)]; rfl
        have hy3_tmp : y₃.stacks tmp = hd :: x.stacks tmp := by
          dsimp only [y₃, y₂, y₁]
          rw [Function.update_of_ne h2.symm, Function.update_self,
            Function.update_of_ne h2.symm, ← hv]
          dsimp only [y₁]; rw [readRegs_eq_val (by decide : rVal ≠ rPres)]; rfl
        have hy3_bits : BitProgram.stackBits y₃.stacks + 1 = BitProgram.stackBits x.stacks := by
          have hstk : y₃.stacks = Function.update
              (Function.update x.stacks src (frameTail tl ++ tail)) tmp (hd :: x.stacks tmp) := by
            funext k
            by_cases hks : k = src
            · subst hks; dsimp only [y₃]; rw [Function.update_self, Function.update_of_ne h2, Function.update_self]
            · by_cases hkt : k = tmp
              · subst hkt; rw [hy3_tmp, Function.update_self]
              · dsimp only [y₃, y₂, y₁]
                rw [Function.update_of_ne hks, Function.update_of_ne hkt, Function.update_of_ne hks,
                  Function.update_of_ne hkt, Function.update_of_ne hks]
          rw [hstk]
          exact stackBits_pop_push_drop x.stacks src tmp h2 hd (!tl.isEmpty) (frameTail tl ++ tail) hxsrc
        refine ⟨3, y₃, Spec.of_eval_local (.seq hy₁ (.seq hy₂ hy₃)) (by omega), tl,
          by dsimp only [y₃]; rw [Function.update_self],
          by dsimp only [y₃]; rw [readRegs_eq_val (by decide : rLoop ≠ rPres)]; rfl, by omega⟩
  have sp₂ : Spec inS outS (mkWhile rLoop (popFrameBody src tmp)) a₁ b₂ nt B :=
    Spec.while inS outS (popFrameBody src tmp) rLoop I B hinit hstep e₂_ev
      ⟨w, ha1_src, ha1_loop, by omega⟩
  have hb2_bits : BitProgram.stackBits b₂.stacks + w.length + 1 = BitProgram.stackBits a.stacks := by omega
  obtain ⟨n₃, b₃, sp₃, hn₃, h3tmp, h3dst, h3o, h3reg, h3bits⟩ :=
    revMove_spec (inS := inS) (outS := outS) (B := B) h3.symm b₂ (by omega)
  have h2dst : b₂.stacks dst = [] :=
    (h2o dst h1.symm h3).trans (by dsimp only [a₁]; rw [Function.update_of_ne h1.symm, hdst])
  refine ⟨1 + (nt + n₃), b₃, Spec.seq sp₁ (Spec.seq sp₂ sp₃), ?_, ?_, ?_, h3tmp, ?_, ?_, ?_⟩
  · have h2t_len : (b₂.stacks tmp).length = w.length := by
      rw [h2tmp]; dsimp only [a₁]; rw [Function.update_of_ne h2.symm, htmp]; simp
    rw [hnt, hn₃, h2t_len]; omega
  · rw [h3o src h2 h1, h2src]
  · rw [h3dst, h2tmp, h2dst]; dsimp only [a₁]; rw [Function.update_of_ne h2.symm, htmp]; simp
  · intro k hks hkd hkt
    rw [h3o k hkt hkd, h2o k hks hkt]; dsimp only [a₁]; rw [Function.update_of_ne hks]
  · exact regPreserved_trans
      (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (regPreserved_trans h2reg h3reg)
  · rw [h3bits, hb2_bits]

theorem popFrame_eval {src dst tmp : Fin S}
    (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (w tail : List Bool) (a : SState)
    (hsrc : a.stacks src = Encoding.frame w ++ tail)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = []) :
    ∃ n b, StructuredCalls.Eval (popFrame src dst tmp) n a b ∧
      n = 8 * w.length + 4 ∧
      b.stacks src = tail ∧ b.stacks dst = w ∧ b.stacks tmp = [] ∧
      (∀ k, k ≠ src → k ≠ dst → k ≠ tmp → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  obtain ⟨n, b, sp, hrest⟩ := popFrame_spec (inS := sIn) (outS := sOut) h1 h2 h3 w tail a hsrc hdst htmp
    (B := BitProgram.stackBits a.stacks + 10) le_rfl
  exact ⟨n, b, sp.1, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hrest.2.2.2.2.1, hrest.2.2.2.2.2.1⟩

/-- Backed frame decoder: pops `Encoding.frame w` onto `dst` while backing up popped bits onto `bak`. -/
def popFrameBackedBody (src bak tmp : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.pop src rVal rPres),
    mkAtom (.push bak rVal),
    mkAtom (.push tmp rVal),
    mkAtom (.pop src rLoop rPres),
    mkAtom (.push bak rLoop)
  ]

def popFrameBacked (src bak dst tmp : Fin S) : SCmd :=
  mkSeqList [
    mkAtom (.pop src rLoop rPres),
    mkAtom (.push bak rLoop),
    mkWhile rLoop (popFrameBackedBody src bak tmp),
    revMove tmp dst
  ]

theorem popFrameBacked_eval {src bak dst tmp : Fin S}
    (hsb : src ≠ bak) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hbd : bak ≠ dst) (hbt : bak ≠ tmp) (hdt : dst ≠ tmp)
    (w tail : List Bool) (a : SState)
    (hsrc : a.stacks src = Encoding.frame w ++ tail)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = []) :
    ∃ n b, StructuredCalls.Eval (popFrameBacked src bak dst tmp) n a b ∧
      n = 10 * w.length + 5 ∧
      b.stacks src = tail ∧
      b.stacks bak = (Encoding.frame w).reverse ++ a.stacks bak ∧
      b.stacks dst = w ∧ b.stacks tmp = [] ∧
      (∀ k, k ≠ src → k ≠ bak → k ≠ dst → k ≠ tmp → b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  have loop_aux : ∀ wc x0,
      x0.stacks src = frameTail wc ++ tail →
      x0.regs rLoop = !wc.isEmpty →
      ∃ n b, StructuredCalls.Eval (mkWhile rLoop (popFrameBackedBody src bak tmp)) n x0 b ∧
        n = 6 * wc.length + 1 ∧
        b.stacks src = tail ∧
        b.stacks bak = (frameTail wc).reverse ++ x0.stacks bak ∧
        b.stacks tmp = wc.reverse ++ x0.stacks tmp ∧
        (∀ k, k ≠ src → k ≠ bak → k ≠ tmp → b.stacks k = x0.stacks k) ∧
        RegPreserved x0 b := by
    intro wc
    induction wc with
    | nil =>
        intro x0 hs hl
        simp only [List.isEmpty_nil, Bool.not_true, frameTail, List.nil_append] at hs hl ⊢
        exact ⟨1, x0, .while_false hl, rfl, hs, by simp, by simp, fun _ _ _ _ => rfl, regPreserved_refl x0⟩
    | cons hd tl ih =>
        intro x0 hs hl
        simp only [List.isEmpty_cons, Bool.not_false] at hl
        rw [frameTail, frame_eq_tag_append_frameTail] at hs
        simp only [List.cons_append] at hs
        let x₁ : SState := ⟨BitProgram.readRegs x0.regs rVal rPres (some hd),
          Function.update x0.stacks src ((!tl.isEmpty) :: (frameTail tl ++ tail))⟩
        have e₁ : StructuredCalls.Eval (mkAtom (.pop src rVal rPres)) 1 x0 x₁ := by
          simpa [x₁, hs] using eval_pop x0 src rVal rPres
        have hv1 : x₁.regs rVal = hd := by
          dsimp only [x₁]; rw [readRegs_eq_val (by decide : rVal ≠ rPres)]; rfl
        let x₂ : SState := ⟨x₁.regs, Function.update x₁.stacks bak (x₁.regs rVal :: x₁.stacks bak)⟩
        have e₂ := eval_push x₁ bak rVal
        let x₃ : SState := ⟨x₂.regs, Function.update x₂.stacks tmp (x₂.regs rVal :: x₂.stacks tmp)⟩
        have e₃ := eval_push x₂ tmp rVal
        have hx3_src : x₃.stacks src = (!tl.isEmpty) :: (frameTail tl ++ tail) := by
          dsimp only [x₃, x₂, x₁]
          rw [Function.update_of_ne hst, Function.update_of_ne hsb, Function.update_self]
        let x₄ : SState := ⟨BitProgram.readRegs x₃.regs rLoop rPres (some (!tl.isEmpty)),
          Function.update x₃.stacks src (frameTail tl ++ tail)⟩
        have e₄ : StructuredCalls.Eval (mkAtom (.pop src rLoop rPres)) 1 x₃ x₄ := by
          simpa [x₄, hx3_src] using eval_pop x₃ src rLoop rPres
        have hl4 : x₄.regs rLoop = !tl.isEmpty := by
          dsimp only [x₄]; rw [readRegs_eq_val (by decide : rLoop ≠ rPres)]; rfl
        let x₅ : SState := ⟨x₄.regs, Function.update x₄.stacks bak (x₄.regs rLoop :: x₄.stacks bak)⟩
        have e₅ := eval_push x₄ bak rLoop
        have hx5_src : x₅.stacks src = frameTail tl ++ tail := by
          dsimp only [x₅, x₄]; rw [Function.update_of_ne hsb, Function.update_self]
        have hx5_bak : x₅.stacks bak = (!tl.isEmpty) :: hd :: x0.stacks bak := by
          dsimp only [x₅]; rw [Function.update_self, hl4]
          dsimp only [x₄, x₃, x₂]
          rw [Function.update_of_ne hsb.symm, Function.update_of_ne hbt, Function.update_self, hv1]
          dsimp only [x₁]; rw [Function.update_of_ne hsb.symm]
        have hx5_tmp : x₅.stacks tmp = hd :: x0.stacks tmp := by
          dsimp only [x₅, x₄, x₃]
          rw [Function.update_of_ne hbt.symm, Function.update_of_ne hst.symm, Function.update_self]
          dsimp only [x₂]; rw [Function.update_of_ne hbt.symm, hv1]
          dsimp only [x₁]; rw [Function.update_of_ne hst.symm]
        obtain ⟨nt, fin, htail, hnt, hfs, hfb, hft, hfo, hreg_t⟩ := ih x₅ hx5_src hl4
        refine ⟨5 + nt + 1, fin, .while_true hl (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))) htail,
          ?_, hfs, ?_, ?_, ?_, ?_⟩
        · simp [List.length_cons, hnt]; omega
        · rw [hfb, hx5_bak, frameTail, frame_eq_tag_append_frameTail]; simp [List.reverse_cons, List.append_assoc]
        · rw [hft, hx5_tmp]; simp [List.reverse_cons]
        · intro k hks hkb hkt
          rw [hfo k hks hkb hkt]
          dsimp only [x₅, x₄, x₃, x₂, x₁]
          rw [Function.update_of_ne hkb, Function.update_of_ne hks, Function.update_of_ne hkt,
            Function.update_of_ne hkb, Function.update_of_ne hks]
        · exact regPreserved_trans
            (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
            (regPreserved_trans
              (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              hreg_t)
  have hsrc' : a.stacks src = (!w.isEmpty) :: (frameTail w ++ tail) := by
    rw [hsrc, frame_eq_tag_append_frameTail, List.cons_append]
  let a₁ : SState := ⟨BitProgram.readRegs a.regs rLoop rPres (some (!w.isEmpty)),
    Function.update a.stacks src (frameTail w ++ tail)⟩
  have e₁ : StructuredCalls.Eval (mkAtom (.pop src rLoop rPres)) 1 a a₁ := by
    simpa [a₁, hsrc'] using eval_pop a src rLoop rPres
  have hl1 : a₁.regs rLoop = !w.isEmpty := by
    dsimp only [a₁]; rw [readRegs_eq_val (by decide : rLoop ≠ rPres)]; rfl
  let a₂ : SState := ⟨a₁.regs, Function.update a₁.stacks bak (a₁.regs rLoop :: a₁.stacks bak)⟩
  have e₂ := eval_push a₁ bak rLoop
  have ha2_src : a₂.stacks src = frameTail w ++ tail := by
    dsimp only [a₂, a₁]; rw [Function.update_of_ne hsb, Function.update_self]
  have ha2_bak : a₂.stacks bak = (!w.isEmpty) :: a.stacks bak := by
    dsimp only [a₂]; rw [Function.update_self, hl1]; dsimp only [a₁]; rw [Function.update_of_ne hsb.symm]
  obtain ⟨nt, b₃, e₃, hnt, h3src, h3bak, h3tmp, h3o, h3reg⟩ := loop_aux w a₂ ha2_src hl1
  obtain ⟨n₄, b₄, e₄, hn₄, h4tmp, h4dst, h4o, h4reg, _, _, _⟩ := revMove_eval hdt.symm b₃
  have h3dst : b₃.stacks dst = [] := by
    rw [h3o dst hsd.symm hbd.symm hdt]
    dsimp only [a₂, a₁]
    rw [Function.update_of_ne hbd.symm, Function.update_of_ne hsd.symm, hdst]
  have h3t : b₃.stacks tmp = w.reverse := by
    rw [h3tmp]; dsimp only [a₂, a₁]
    rw [Function.update_of_ne hbt.symm, Function.update_of_ne hst.symm, htmp]; simp
  refine ⟨1 + (1 + (nt + n₄)), b₄, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, ?_, ?_, ?_, h4tmp, ?_, ?_⟩
  · rw [hn₄, hnt, h3t]; simp; omega
  · rw [h4o src hst hsd, h3src]
  · rw [h4o bak hbt hbd, h3bak, ha2_bak, frame_eq_tag_append_frameTail]; simp
  · rw [h4dst, h3t, h3dst]; simp
  · intro k hks hkb hkd hkt
    rw [h4o k hkt hkd, h3o k hks hkb hkt]
    dsimp only [a₂, a₁]
    rw [Function.update_of_ne hkb, Function.update_of_ne hks]
  · exact regPreserved_trans
      (regPreserved_readRegs _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (regPreserved_trans h3reg h4reg)

/-- 17. Nat-list decoder `popNatFrame` (`flag` gets `!xs.isEmpty`; other caller flags preserved). -/
def popNatFrame (src dst tmp : Fin S) (flag : Fin R) : SCmd :=
  mkSeqList [
    clearStack dst,
    mkAtom (.pop src flag rPres),
    mkIte flag
      (mkSeqList [popFrame src dst tmp, stripZeros dst tmp, mkAtom (.set flag true)])
      (mkAtom (.set flag false))
  ]

theorem popNatFrame_eval {src dst tmp : Fin S}
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (flag : Fin R) (hf_pres : flag ≠ rPres)
    (hf_in : flag = rHasR ∨ flag = rHasNext ∨ flag = rFlag)
    (xs : List ℕ) (a : SState)
    (hsrc : a.stacks src = encodeNatListBin xs) (htmp : a.stacks tmp = []) :
    ∃ n b, StructuredCalls.Eval (popNatFrame src dst tmp flag) n a b ∧
      n ≤ 3 * (a.stacks dst).length +
          (match xs with | [] => 8 | x :: _ => 25 * (countWord x).length + 25) ∧
      b.stacks src = (match xs with | [] => [] | _ :: rest => encodeNatListBin rest) ∧
      b.stacks dst = (match xs with | [] => [] | x :: _ => x.bits) ∧
      b.stacks tmp = [] ∧
      (∀ k, k ≠ src → k ≠ dst → k ≠ tmp → b.stacks k = a.stacks k) ∧
      b.regs flag = !xs.isEmpty ∧
      (rFound ≠ flag → b.regs rFound = a.regs rFound) ∧
      (rHasR ≠ flag → b.regs rHasR = a.regs rHasR) ∧
      (rHasNext ≠ flag → b.regs rHasNext = a.regs rHasNext) := by
  have hf9 : rFound ≠ flag := by rcases hf_in with rfl | rfl | rfl <;> decide
  obtain ⟨n₁, b₁, e₁, hn₁, h1d, h1o, h1reg⟩ := clearStack_eval dst a
  have h1s : b₁.stacks src = encodeNatListBin xs := (h1o src hsd).trans hsrc
  have h1t : b₁.stacks tmp = [] := (h1o tmp hdt.symm).trans htmp
  cases xs with
  | nil =>
      simp only [encodeNatListBin, Encoding.encodeList] at h1s
      let b₂ : SState := ⟨BitProgram.readRegs b₁.regs flag rPres (some false),
        Function.update b₁.stacks src []⟩
      have e₂ : StructuredCalls.Eval (mkAtom (.pop src flag rPres)) 1 b₁ b₂ := by
        simpa [b₂, h1s] using eval_pop b₁ src flag rPres
      have hf2 : b₂.regs flag = false := by
        dsimp only [b₂]; rw [readRegs_eq_val hf_pres]; rfl
      let b₃ : SState := ⟨Function.update b₂.regs flag false, b₂.stacks⟩
      have e₃ := eval_set b₂ flag false
      refine ⟨n₁ + (1 + (1 + 1)), b₃, .seq e₁ (.seq e₂ (.ite_false hf2 e₃)), by dsimp only; omega,
        by dsimp only; simp [b₃, b₂],
        by dsimp only; simp [b₃, b₂, Function.update_of_ne hsd.symm, h1d],
        by simp [b₃, b₂, Function.update_of_ne hst.symm, h1t],
        fun k hks hkd hkt => by simp [b₃, b₂, Function.update_of_ne hks, h1o k hkd],
        by simp [b₃],
        fun h => by dsimp only [b₃, b₂]; rw [Function.update_of_ne h, readRegs_eq_other h (by decide), h1reg.1],
        fun h => by dsimp only [b₃, b₂]; rw [Function.update_of_ne h, readRegs_eq_other h (by decide), h1reg.2.1],
        fun h => by dsimp only [b₃, b₂]; rw [Function.update_of_ne h, readRegs_eq_other h (by decide), h1reg.2.2]⟩
  | cons x rest =>
      simp only [encodeNatListBin, Encoding.encodeList] at h1s
      let b₂ : SState := ⟨BitProgram.readRegs b₁.regs flag rPres (some true),
        Function.update b₁.stacks src (Encoding.frame (countWord x) ++ encodeNatListBin rest)⟩
      have e₂ : StructuredCalls.Eval (mkAtom (.pop src flag rPres)) 1 b₁ b₂ := by
        simpa [b₂, h1s, encodeNatListBin] using eval_pop b₁ src flag rPres
      have hf2 : b₂.regs flag = true := by
        dsimp only [b₂]; rw [readRegs_eq_val hf_pres]; rfl
      obtain ⟨n₃, b₃, e₃, hn₃, h3s, h3d, h3t, h3o, h3reg⟩ :=
        popFrame_eval hsd hst hdt (countWord x) (encodeNatListBin rest) b₂
          (by simp [b₂]) (by simp [b₂, Function.update_of_ne hsd.symm, h1d])
          (by simp [b₂, Function.update_of_ne hst.symm, h1t])
      obtain ⟨n₄, b₄, e₄, hn₄, h4d, h4t, h4o, h4reg⟩ := stripZeros_eval hdt b₃ h3t
      let b₅ : SState := ⟨Function.update b₄.regs flag true, b₄.stacks⟩
      have e₅ := eval_set b₄ flag true
      have hb2_reg : ∀ r : Fin R, r ≠ flag → r ≠ rPres → b₂.regs r = b₁.regs r := fun r hr1 hr2 => by
        dsimp only [b₂]; exact readRegs_eq_other hr1 hr2 (some true)
      refine ⟨n₁ + (1 + (n₃ + (n₄ + 1) + 1)), b₅,
        .seq e₁ (.seq e₂ (.ite_true hf2 (.seq e₃ (.seq e₄ e₅)))), ?_, ?_, ?_, h4t, ?_,
        by simp [b₅], ?_, ?_, ?_⟩
      · rw [hn₁, hn₃, h3d] at *; dsimp only at *; omega
      · dsimp only; dsimp only [b₅]; rw [h4o src hsd hst, h3s]
      · dsimp only; dsimp only [b₅]; rw [h4d, h3d, toNat_countWord]
      · intro k hks hkd hkt
        dsimp only [b₅]; rw [h4o k hkd hkt, h3o k hks hkd hkt]
        dsimp only [b₂]; rw [Function.update_of_ne hks, h1o k hkd]
      · intro h
        have hr1 : b₄.regs rFound = b₂.regs rFound := (h3reg.1.trans h4reg.1).symm
        dsimp only [b₅]; rw [Function.update_of_ne h, hr1, hb2_reg rFound h (by decide), h1reg.1]
      · intro h
        have hr1 : b₄.regs rHasR = b₂.regs rHasR := (h3reg.2.1.trans h4reg.2.1).symm
        dsimp only [b₅]; rw [Function.update_of_ne h, hr1, hb2_reg rHasR h (by decide), h1reg.2.1]
      · intro h
        have hr1 : b₄.regs rHasNext = b₂.regs rHasNext := (h3reg.2.2.trans h4reg.2.2).symm
        dsimp only [b₅]; rw [Function.update_of_ne h, hr1, hb2_reg rHasNext h (by decide), h1reg.2.2]

/-- Backed Nat-list decoder: pops one Nat from `src` onto `dst` while backing up onto `bak`. -/
def popNatFrameBacked (src bak dst tmp : Fin S) (flag : Fin R) : SCmd :=
  mkSeqList [
    clearStack dst,
    mkAtom (.pop src flag rPres),
    mkAtom (.push bak flag),
    mkIte flag
      (mkSeqList [popFrameBacked src bak dst tmp, stripZeros dst tmp, mkAtom (.set flag true)])
      (mkAtom (.set flag false))
  ]

theorem popNatFrameBacked_eval {src bak dst tmp : Fin S}
    (hsb : src ≠ bak) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hbd : bak ≠ dst) (hbt : bak ≠ tmp) (hdt : dst ≠ tmp)
    (flag : Fin R) (hf_pres : flag ≠ rPres)
    (hf_in : flag = rHasR ∨ flag = rHasNext ∨ flag = rFlag)
    (xs : List ℕ) (a : SState)
    (hsrc : a.stacks src = encodeNatListBin xs) (htmp : a.stacks tmp = []) :
    ∃ n b, StructuredCalls.Eval (popNatFrameBacked src bak dst tmp flag) n a b ∧
      n ≤ 3 * (a.stacks dst).length +
          (match xs with | [] => 9 | x :: _ => 28 * (countWord x).length + 28) ∧
      b.stacks src = (match xs with | [] => [] | _ :: rest => encodeNatListBin rest) ∧
      b.stacks bak = (match xs with
        | [] => false :: a.stacks bak
        | x :: _ => (true :: Encoding.frame (countWord x)).reverse ++ a.stacks bak) ∧
      b.stacks dst = (match xs with | [] => [] | x :: _ => x.bits) ∧
      b.stacks tmp = [] ∧
      (∀ k, k ≠ src → k ≠ bak → k ≠ dst → k ≠ tmp → b.stacks k = a.stacks k) ∧
      b.regs flag = !xs.isEmpty ∧
      (rFound ≠ flag → b.regs rFound = a.regs rFound) ∧
      (rHasR ≠ flag → b.regs rHasR = a.regs rHasR) ∧
      (rHasNext ≠ flag → b.regs rHasNext = a.regs rHasNext) := by
  obtain ⟨n₁, b₁, e₁, hn₁, h1d, h1o, h1reg⟩ := clearStack_eval dst a
  have h1s : b₁.stacks src = encodeNatListBin xs := (h1o src hsd).trans hsrc
  have h1t : b₁.stacks tmp = [] := (h1o tmp hdt.symm).trans htmp
  have h1b : b₁.stacks bak = a.stacks bak := h1o bak hbd
  cases xs with
  | nil =>
      simp only [encodeNatListBin, Encoding.encodeList] at h1s
      let b₂ : SState := ⟨BitProgram.readRegs b₁.regs flag rPres (some false),
        Function.update b₁.stacks src []⟩
      have e₂ : StructuredCalls.Eval (mkAtom (.pop src flag rPres)) 1 b₁ b₂ := by
        simpa [b₂, h1s] using eval_pop b₁ src flag rPres
      have hf2 : b₂.regs flag = false := by
        dsimp only [b₂]; rw [readRegs_eq_val hf_pres]; rfl
      let b₃ : SState := ⟨b₂.regs, Function.update b₂.stacks bak (b₂.regs flag :: b₂.stacks bak)⟩
      have e₃ := eval_push b₂ bak flag
      let b₄ : SState := ⟨Function.update b₃.regs flag false, b₃.stacks⟩
      have e₄ := eval_set b₃ flag false
      refine ⟨n₁ + (1 + (1 + (1 + 1))), b₄, .seq e₁ (.seq e₂ (.seq e₃ (.ite_false hf2 e₄))),
        by dsimp only; omega,
        by dsimp only; simp [b₄, b₃, b₂, Function.update_of_ne hsb],
        by dsimp only; dsimp only [b₄, b₃]; rw [Function.update_self, hf2]; dsimp only [b₂]
           rw [Function.update_of_ne hsb.symm, h1b],
        by dsimp only; simp [b₄, b₃, b₂, Function.update_of_ne hbd.symm, Function.update_of_ne hsd.symm, h1d],
        by simp [b₄, b₃, b₂, Function.update_of_ne hbt.symm, Function.update_of_ne hst.symm, h1t],
        fun k hks hkb hkd hkt => by
          dsimp only [b₄, b₃, b₂]
          rw [Function.update_of_ne hkb, Function.update_of_ne hks, h1o k hkd],
        by simp [b₄],
        fun h => by dsimp only [b₄, b₃, b₂]; rw [Function.update_of_ne h, readRegs_eq_other h (by decide), h1reg.1],
        fun h => by dsimp only [b₄, b₃, b₂]; rw [Function.update_of_ne h, readRegs_eq_other h (by decide), h1reg.2.1],
        fun h => by dsimp only [b₄, b₃, b₂]; rw [Function.update_of_ne h, readRegs_eq_other h (by decide), h1reg.2.2]⟩
  | cons x rest =>
      simp only [encodeNatListBin, Encoding.encodeList] at h1s
      let b₂ : SState := ⟨BitProgram.readRegs b₁.regs flag rPres (some true),
        Function.update b₁.stacks src (Encoding.frame (countWord x) ++ encodeNatListBin rest)⟩
      have e₂ : StructuredCalls.Eval (mkAtom (.pop src flag rPres)) 1 b₁ b₂ := by
        simpa [b₂, h1s, encodeNatListBin] using eval_pop b₁ src flag rPres
      have hf2 : b₂.regs flag = true := by
        dsimp only [b₂]; rw [readRegs_eq_val hf_pres]; rfl
      let b₃ : SState := ⟨b₂.regs, Function.update b₂.stacks bak (b₂.regs flag :: b₂.stacks bak)⟩
      have e₃ := eval_push b₂ bak flag
      have hb3_src : b₃.stacks src = Encoding.frame (countWord x) ++ encodeNatListBin rest := by
        simp [b₃, b₂, Function.update_of_ne hsb]
      have hb3_dst : b₃.stacks dst = [] := by
        simp [b₃, b₂, Function.update_of_ne hbd.symm, Function.update_of_ne hsd.symm, h1d]
      have hb3_tmp : b₃.stacks tmp = [] := by
        simp [b₃, b₂, Function.update_of_ne hbt.symm, Function.update_of_ne hst.symm, h1t]
      have hb3_bak : b₃.stacks bak = true :: a.stacks bak := by
        dsimp only [b₃]; rw [Function.update_self, hf2]; dsimp only [b₂]
        rw [Function.update_of_ne hsb.symm, h1b]
      obtain ⟨n₄, b₄, e₄, hn₄, h4s, h4b, h4d, h4t, h4o, h4reg⟩ :=
        popFrameBacked_eval hsb hsd hst hbd hbt hdt (countWord x) (encodeNatListBin rest) b₃
          hb3_src hb3_dst hb3_tmp
      obtain ⟨n₅, b₅, e₅, hn₅, h5d, h5t, h5o, h5reg⟩ := stripZeros_eval hdt b₄ h4t
      let b₆ : SState := ⟨Function.update b₅.regs flag true, b₅.stacks⟩
      have e₆ := eval_set b₅ flag true
      have hb2_reg : ∀ r : Fin R, r ≠ flag → r ≠ rPres → b₂.regs r = b₁.regs r := fun r hr1 hr2 => by
        dsimp only [b₂]; exact readRegs_eq_other hr1 hr2 (some true)
      refine ⟨n₁ + (1 + (1 + (n₄ + (n₅ + 1) + 1))), b₆,
        .seq e₁ (.seq e₂ (.seq e₃ (.ite_true hf2 (.seq e₄ (.seq e₅ e₆))))), ?_, ?_, ?_, ?_, h5t, ?_,
        by simp [b₆], ?_, ?_, ?_⟩
      · rw [hn₁, hn₄]; rw [h4d] at hn₅; dsimp only; omega
      · dsimp only; dsimp only [b₆]; rw [h5o src hsd hst, h4s]
      · dsimp only; dsimp only [b₆]; rw [h5o bak hbd hbt, h4b, hb3_bak]; simp [List.reverse_cons, List.append_assoc]
      · dsimp only; dsimp only [b₆]; rw [h5d, h4d, toNat_countWord]
      · intro k hks hkb hkd hkt
        dsimp only [b₆]; rw [h5o k hkd hkt, h4o k hks hkb hkd hkt]
        dsimp only [b₃, b₂]; rw [Function.update_of_ne hkb, Function.update_of_ne hks, h1o k hkd]
      · intro h
        have hr1 : b₅.regs rFound = b₃.regs rFound := (h4reg.1.trans h5reg.1).symm
        dsimp only [b₆]; rw [Function.update_of_ne h, hr1, hb2_reg rFound h (by decide), h1reg.1]
      · intro h
        have hr1 : b₅.regs rHasR = b₃.regs rHasR := (h4reg.2.1.trans h5reg.2.1).symm
        dsimp only [b₆]; rw [Function.update_of_ne h, hr1, hb2_reg rHasR h (by decide), h1reg.2.1]
      · intro h
        have hr1 : b₅.regs rHasNext = b₃.regs rHasNext := (h4reg.2.2.trans h5reg.2.2).symm
        dsimp only [b₆]; rw [Function.update_of_ne h, hr1, hb2_reg rHasNext h (by decide), h1reg.2.2]

/-- 18. Input unpacker `unpackCmd`: unpacks `[countWord p, encodeNatListBin fs, encodeNatListBin us]`. -/
def unpackTailCmd : SCmd :=
  mkSeqList [
    clearStack sIn,
    copyStack sP sN sTmp1,
    mkAtom (.set rBit true),
    mkAtom (.push sTmp3 rBit),
    subInPlace sN sTmp3 sTmp1 sTmp2,
    clearStack sTmp3,
    mkAtom (.set rBit true),
    mkAtom (.push sAns rBit)
  ]

def unpackCmd : SCmd :=
  mkSeqList [
    mkAtom (.pop sIn rTmp1 rPres),
    popFrame sIn sP sTmp1,
    stripZeros sP sTmp1,
    mkAtom (.pop sIn rTmp1 rPres),
    popFrame sIn sFs sTmp1,
    mkAtom (.pop sIn rTmp1 rPres),
    popFrame sIn sUs sTmp1,
    unpackTailCmd
  ]

theorem unpack_spec {p : ℕ} (hp2 : 2 ≤ p) (fs us : List ℕ) :
    let input := Encoding.encodeList id [countWord p, encodeNatListBin fs, encodeNatListBin us]
    let B := input.length + 70 * (bitLen p + 1) + 160
    ∃ n b, Spec sIn sOut unpackCmd (StructuredProgram.ioState sIn input) b n B ∧
      n ≤ 10 * input.length + 70 * (bitLen p + 1) + 160 ∧
      b.stacks sP = p.bits ∧ b.stacks sN = (p - 1).bits ∧ b.stacks sAns = [true] ∧
      b.stacks sFs = encodeNatListBin fs ∧ b.stacks sUs = encodeNatListBin us ∧
      (∀ k : Fin S, k ≠ sP → k ≠ sN → k ≠ sAns → k ≠ sFs → k ≠ sUs → b.stacks k = []) := by
  let input := Encoding.encodeList id [countWord p, encodeNatListBin fs, encodeNatListBin us]
  let B := input.length + 70 * (bitLen p + 1) + 160
  let a₀ : SState := StructuredProgram.ioState sIn input
  have hbits0 : BitProgram.stackBits a₀.stacks = input.length := ioState_stackBits input
  have hcw : (countWord p).length ≤ bitLen p + 1 :=
    (countWord_length_le p).trans (max_le (by omega) (prime_bits_length_le hp2))
  have hlen_in : input.length = 2 * (countWord p).length + 2 * (encodeNatListBin fs).length +
      2 * (encodeNatListBin us).length + 7 := by
    simp [input, Encoding.encodeList, frame_length]; omega
  -- Step 1: pop sIn
  let tail1 := Encoding.frame (countWord p) ++
    (true :: (Encoding.frame (encodeNatListBin fs) ++
    (true :: (Encoding.frame (encodeNatListBin us) ++ [false]))))
  let a₁ : SState := ⟨BitProgram.readRegs a₀.regs rTmp1 rPres (some true), Function.update a₀.stacks sIn tail1⟩
  have e₁ : StructuredCalls.Eval (mkAtom (.pop sIn rTmp1 rPres)) 1 a₀ a₁ := by
    simpa [a₁, a₀, input, tail1, Encoding.encodeList, List.cons_append] using
      eval_pop a₀ sIn rTmp1 rPres
  have sp₁ : Spec sIn sOut (mkAtom (.pop sIn rTmp1 rPres)) a₀ a₁ 1 B :=
    Spec.of_eval_local e₁ (by omega)
  have h1bits : BitProgram.stackBits a₁.stacks ≤ input.length := by
    have hu := BitProgram.stackBits_update a₀.stacks sIn tail1
    have ha0_in : (a₀.stacks sIn).length = input.length := by
      simp [a₀, StructuredProgram.ioState]
    have ht1 : tail1.length + 1 = input.length := by simp [tail1, hlen_in, frame_length]; omega
    rw [hbits0, ha0_in] at hu
    dsimp only [a₁]; omega
  -- Step 2: popFrame sIn sP sTmp1
  obtain ⟨n₂, a₂, sp₂, hn₂, h2in, h2P, h2t1, h2o, _, h2bits⟩ :=
    popFrame_spec (inS := sIn) (outS := sOut) (src := sIn) (dst := sP) (tmp := sTmp1) (B := B)
      (by decide) (by decide) (by decide)
      (countWord p) (true :: (Encoding.frame (encodeNatListBin fs) ++
        (true :: (Encoding.frame (encodeNatListBin us) ++ [false])))) a₁
      (by dsimp only [a₁]; rw [Function.update_self])
      (by dsimp only [a₁, a₀]; rw [Function.update_of_ne (by decide : sP ≠ sIn)]; simp [StructuredProgram.ioState])
      (by dsimp only [a₁, a₀]; rw [Function.update_of_ne (by decide : sTmp1 ≠ sIn)]; simp [StructuredProgram.ioState])
      (by omega)
  -- Step 3: stripZeros sP sTmp1
  obtain ⟨n₃, a₃, e₃, hn₃, h3P, h3t1, h3o, _⟩ := stripZeros_eval (by decide : sP ≠ sTmp1) a₂ h2t1
  have h3P' : a₃.stacks sP = p.bits := by rw [h3P, h2P, toNat_countWord]
  have h2bits_le : BitProgram.stackBits a₂.stacks ≤ input.length := by omega
  have sp₃ : Spec sIn sOut (stripZeros sP sTmp1) a₂ a₃ n₃ B :=
    Spec.of_eval_local e₃ (by rw [h2P] at hn₃; omega)
  have h3bits : BitProgram.stackBits a₃.stacks ≤ input.length := by
    have hp_ne : p ≠ 0 := by omega
    have hP_le : (a₃.stacks sP).length ≤ (a₂.stacks sP).length := by
      rw [h3P', h2P]; simp [countWord, hp_ne]
    have hu := Finset.sum_le_sum (f := fun k => (a₃.stacks k).length) (g := fun k => (a₂.stacks k).length)
      (s := Finset.univ) (fun k _ => by
        by_cases hkP : k = sP
        · subst hkP; exact hP_le
        · by_cases hkt : k = sTmp1
          · subst hkt; rw [h3t1, h2t1]
          · rw [h3o k hkP hkt])
    exact hu.trans h2bits_le
  -- Step 4: pop sIn
  let tail4 := Encoding.frame (encodeNatListBin fs) ++
    (true :: (Encoding.frame (encodeNatListBin us) ++ [false]))
  have h3in : a₃.stacks sIn = true :: tail4 := by
    rw [h3o sIn (by decide) (by decide), h2in]
  let a₄ : SState := ⟨BitProgram.readRegs a₃.regs rTmp1 rPres (some true),
    Function.update a₃.stacks sIn tail4⟩
  have e₄ : StructuredCalls.Eval (mkAtom (.pop sIn rTmp1 rPres)) 1 a₃ a₄ := by
    have ep := eval_pop a₃ sIn rTmp1 rPres
    rw [h3in] at ep
    exact ep
  have sp₄ : Spec sIn sOut (mkAtom (.pop sIn rTmp1 rPres)) a₃ a₄ 1 B :=
    Spec.of_eval_local e₄ (by omega)
  have h4bits : BitProgram.stackBits a₄.stacks ≤ input.length := by
    have hu := BitProgram.stackBits_update a₃.stacks sIn tail4
    rw [h3in] at hu; simp only [List.length_cons] at hu
    dsimp only [a₄]; omega
  -- Step 5: popFrame sIn sFs sTmp1
  obtain ⟨n₅, a₅, sp₅, hn₅, h5in, h5Fs, h5t1, h5o, _, h5bits⟩ :=
    popFrame_spec (inS := sIn) (outS := sOut) (src := sIn) (dst := sFs) (tmp := sTmp1) (B := B)
      (by decide) (by decide) (by decide)
      (encodeNatListBin fs) (true :: (Encoding.frame (encodeNatListBin us) ++ [false])) a₄
      (by dsimp only [a₄]; rw [Function.update_self])
      (by dsimp only [a₄]; rw [Function.update_of_ne (by decide : sFs ≠ sIn),
            h3o sFs (by decide) (by decide), h2o sFs (by decide) (by decide) (by decide)]
          dsimp only [a₁, a₀]; rw [Function.update_of_ne (by decide : sFs ≠ sIn)]; simp [StructuredProgram.ioState])
      (by dsimp only [a₄]; rw [Function.update_of_ne (by decide : sTmp1 ≠ sIn), h3t1])
      (by omega)
  -- Step 6: pop sIn
  let tail6 := Encoding.frame (encodeNatListBin us) ++ [false]
  let a₆ : SState := ⟨BitProgram.readRegs a₅.regs rTmp1 rPres (some true),
    Function.update a₅.stacks sIn tail6⟩
  have e₆ : StructuredCalls.Eval (mkAtom (.pop sIn rTmp1 rPres)) 1 a₅ a₆ := by
    have h5in' : a₅.stacks sIn = true :: tail6 := h5in
    have ep := eval_pop a₅ sIn rTmp1 rPres
    rw [h5in'] at ep
    exact ep
  have sp₆ : Spec sIn sOut (mkAtom (.pop sIn rTmp1 rPres)) a₅ a₆ 1 B :=
    Spec.of_eval_local e₆ (by omega)
  have h6bits : BitProgram.stackBits a₆.stacks ≤ input.length := by
    have h5in' : a₅.stacks sIn = true :: tail6 := h5in
    have hu := BitProgram.stackBits_update a₅.stacks sIn tail6
    rw [h5in'] at hu; simp only [List.length_cons] at hu
    dsimp only [a₆]; omega
  -- Step 7: popFrame sIn sUs sTmp1
  obtain ⟨n₇, a₇, sp₇, hn₇, h7in, h7Us, h7t1, h7o, _, h7bits⟩ :=
    popFrame_spec (inS := sIn) (outS := sOut) (src := sIn) (dst := sUs) (tmp := sTmp1) (B := B)
      (by decide) (by decide) (by decide)
      (encodeNatListBin us) [false] a₆
      (by dsimp only [a₆]; rw [Function.update_self])
      (by dsimp only [a₆]; rw [Function.update_of_ne (by decide : sUs ≠ sIn),
            h5o sUs (by decide) (by decide) (by decide)]
          dsimp only [a₄]; rw [Function.update_of_ne (by decide : sUs ≠ sIn),
            h3o sUs (by decide) (by decide), h2o sUs (by decide) (by decide) (by decide)]
          dsimp only [a₁, a₀]; rw [Function.update_of_ne (by decide : sUs ≠ sIn)]; simp [StructuredProgram.ioState])
      (by dsimp only [a₆]; rw [Function.update_of_ne (by decide : sTmp1 ≠ sIn), h5t1])
      (by omega)
  have h7bits_le : BitProgram.stackBits a₇.stacks ≤ input.length := by omega
  have h7P : a₇.stacks sP = p.bits := by
    rw [h7o sP (by decide) (by decide) (by decide)]
    dsimp only [a₆]; rw [Function.update_of_ne (by decide : sP ≠ sIn),
      h5o sP (by decide) (by decide) (by decide)]
    dsimp only [a₄]; rw [Function.update_of_ne (by decide : sP ≠ sIn), h3P']
  have h7Fs : a₇.stacks sFs = encodeNatListBin fs := by
    rw [h7o sFs (by decide) (by decide) (by decide)]
    dsimp only [a₆]; rw [Function.update_of_ne (by decide : sFs ≠ sIn), h5Fs]
  have h7zero : ∀ k : Fin S, k ≠ sIn → k ≠ sP → k ≠ sFs → k ≠ sUs → a₇.stacks k = [] := by
    intro k hki hkP hkFs hkUs
    by_cases hkt1 : k = sTmp1
    · subst hkt1; exact h7t1
    · rw [h7o k hki hkUs hkt1]; dsimp only [a₆]; rw [Function.update_of_ne hki, h5o k hki hkFs hkt1]
      dsimp only [a₄]; rw [Function.update_of_ne hki, h3o k hkP hkt1, h2o k hki hkP hkt1]
      dsimp only [a₁, a₀]; rw [Function.update_of_ne hki]
      split_ifs <;> simp_all
  -- Step 8: unpackTailCmd
  obtain ⟨nt₁, t₁, et₁, hnt1, ht1_in, ht1_o, _⟩ := clearStack_eval sIn a₇
  have ht1_P : t₁.stacks sP = p.bits := (ht1_o sP (by decide)).trans h7P
  have ht1_t1 : t₁.stacks sTmp1 = [] := (ht1_o sTmp1 (by decide)).trans (h7zero sTmp1 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨nt₂, t₂, et₂, hnt2, ht2_P, ht2_N, ht2_t1, ht2_o, _⟩ :=
    copyStack_eval (by decide : sP ≠ sN) (by decide : sP ≠ sTmp1) (by decide : sN ≠ sTmp1) t₁ ht1_t1
  let t₃ : SState := ⟨Function.update t₂.regs rBit true, t₂.stacks⟩
  have et₃ := eval_set t₂ rBit true
  let t₄ : SState := ⟨t₃.regs, Function.update t₃.stacks sTmp3 (true :: t₃.stacks sTmp3)⟩
  have et₄ : StructuredCalls.Eval (mkAtom (.push sTmp3 rBit)) 1 t₃ t₄ := by
    simpa [t₄, t₃] using eval_push t₃ sTmp3 rBit
  have ht4_N : t₄.stacks sN = p.bits := by
    simp [t₄, t₃, Function.update_of_ne (by decide : sN ≠ sTmp3), ht2_N, ht1_P]
  have ht4_t3 : t₄.stacks sTmp3 = [true] := by
    dsimp only [t₄, t₃]; rw [Function.update_self, ht2_o sTmp3 (by decide) (by decide),
      ht1_o sTmp3 (by decide), h7zero sTmp3 (by decide) (by decide) (by decide) (by decide)]
  have h1le_p : BinaryArithmetic.toNat (t₄.stacks sTmp3) ≤ BinaryArithmetic.toNat (t₄.stacks sN) := by
    rw [ht4_t3, ht4_N, toNat_bits]; simp [BinaryArithmetic.toNat, bitVal_true]; omega
  obtain ⟨nt₅, t₅, et₅, hnt5, ht5_N, ht5_t3, ht5_t1, ht5_t2, ht5_o, _⟩ :=
    subInPlace_eval (by decide : sN ≠ sTmp3) (by decide : sN ≠ sTmp1) (by decide : sN ≠ sTmp2)
      (by decide : sTmp3 ≠ sTmp1) (by decide : sTmp3 ≠ sTmp2) (by decide : sTmp1 ≠ sTmp2)
      t₄ (by simp [t₄, t₃, Function.update_of_ne (by decide : sTmp1 ≠ sTmp3), ht2_t1])
      (by simp [t₄, t₃, Function.update_of_ne (by decide : sTmp2 ≠ sTmp3), ht2_o sTmp2 (by decide) (by decide),
            ht1_o sTmp2 (by decide), h7zero sTmp2 (by decide) (by decide) (by decide) (by decide)])
      h1le_p
  obtain ⟨nt₆, t₆, et₆, hnt6, ht6_t3, ht6_o, _⟩ := clearStack_eval sTmp3 t₅
  let t₇ : SState := ⟨Function.update t₆.regs rBit true, t₆.stacks⟩
  have et₇ := eval_set t₆ rBit true
  let t₈ : SState := ⟨t₇.regs, Function.update t₇.stacks sAns (true :: t₇.stacks sAns)⟩
  have et₈ : StructuredCalls.Eval (mkAtom (.push sAns rBit)) 1 t₇ t₈ := by
    simpa [t₈, t₇] using eval_push t₇ sAns rBit
  have ht_ev : StructuredCalls.Eval unpackTailCmd (nt₁ + (nt₂ + (1 + (1 + (nt₅ + (nt₆ + (1 + 1))))))) a₇ t₈ :=
    .seq et₁ (.seq et₂ (.seq et₃ (.seq et₄ (.seq et₅ (.seq et₆ (.seq et₇ et₈))))))
  have hnt_bd : nt₁ + (nt₂ + (1 + (1 + (nt₅ + (nt₆ + (1 + 1)))))) ≤ 45 * (bitLen p + 1) + 106 := by
    have hp_len : p.bits.length ≤ bitLen p + 1 := prime_bits_length_le hp2
    rw [h7in] at hnt1
    rw [ht1_P, ht1_o sN (by decide), h7zero sN (by decide) (by decide) (by decide) (by decide)] at hnt2
    rw [ht4_N, ht4_t3] at hnt5
    rw [ht5_t3, ht4_t3] at hnt6
    simp only [List.length_singleton, List.length_nil] at hnt1 hnt2 hnt5 hnt6
    omega
  have sp₈ : Spec sIn sOut unpackTailCmd a₇ t₈ (nt₁ + (nt₂ + (1 + (1 + (nt₅ + (nt₆ + (1 + 1))))))) B :=
    Spec.of_eval_local ht_ev (by omega)
  have ht_keep : ∀ k : Fin S, k ≠ sIn → k ≠ sN → k ≠ sAns → k ≠ sTmp1 → k ≠ sTmp2 → k ≠ sTmp3 →
      t₈.stacks k = a₇.stacks k := fun k hkIn hkN hkAns hkt1 hkt2 hkt3 => by
    dsimp only [t₈, t₇]
    rw [Function.update_of_ne hkAns, ht6_o k hkt3, ht5_o k hkN hkt3 hkt1 hkt2,
      show t₄.stacks k = t₂.stacks k from Function.update_of_ne hkt3 _ _,
      ht2_o k hkN hkt1, ht1_o k hkIn]
  refine ⟨1 + (n₂ + (n₃ + (1 + (n₅ + (1 + (n₇ + (nt₁ + (nt₂ + (1 + (1 + (nt₅ + (nt₆ + (1 + 1))))))))))))), t₈,
    Spec.seq sp₁ (Spec.seq sp₂ (Spec.seq sp₃ (Spec.seq sp₄ (Spec.seq sp₅ (Spec.seq sp₆ (Spec.seq sp₇ sp₈)))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [input] at hlen_in; rw [h2P] at hn₃; omega
  · rw [ht_keep sP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h7P]
  · simp only [t₈, t₇, Function.update_of_ne (by decide : sN ≠ sAns), ht6_o sN (by decide), ht5_N,
      ht4_N, ht4_t3, toNat_bits, BinaryArithmetic.toNat, bitVal_true]
  · dsimp only [t₈, t₇]; rw [Function.update_self, ht6_o sAns (by decide),
      ht5_o sAns (by decide) (by decide) (by decide) (by decide)]
    simp only [t₄, t₃, Function.update_of_ne (by decide : sAns ≠ sTmp3),
      ht2_o sAns (by decide) (by decide), ht1_o sAns (by decide),
      h7zero sAns (by decide) (by decide) (by decide) (by decide)]
  · rw [ht_keep sFs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h7Fs]
  · rw [ht_keep sUs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h7Us]
  · intro k hkP hkN hkAns hkFs hkUs
    by_cases hkIn : k = sIn
    · subst hkIn; dsimp only [t₈, t₇]
      rw [Function.update_of_ne (by decide), ht6_o sIn (by decide),
        ht5_o sIn (by decide) (by decide) (by decide) (by decide)]
      simp only [t₄, t₃, Function.update_of_ne (by decide : sIn ≠ sTmp3),
        ht2_o sIn (by decide) (by decide), ht1_in]
    · by_cases hkt1 : k = sTmp1
      · subst hkt1; dsimp only [t₈, t₇]
        rw [Function.update_of_ne (by decide), ht6_o sTmp1 (by decide), ht5_t1]
      · by_cases hkt2 : k = sTmp2
        · subst hkt2; dsimp only [t₈, t₇]
          rw [Function.update_of_ne (by decide), ht6_o sTmp2 (by decide), ht5_t2]
        · by_cases hkt3 : k = sTmp3
          · subst hkt3; dsimp only [t₈, t₇]; rw [Function.update_of_ne (by decide), ht6_t3]
          · rw [ht_keep k hkIn hkN hkAns hkt1 hkt2 hkt3, h7zero k hkIn hkP hkFs hkUs]

/-! ### Section 4 Part 2: Witness search, sorted-run scan loop, finalizer, and `mainCmd` -/

theorem bits_eq_one_iff (n : ℕ) : n.bits = [true] ↔ n = 1 := by
  constructor
  · intro h
    have ht := congrArg BinaryArithmetic.toNat h
    rw [toNat_bits] at ht
    simpa [BinaryArithmetic.toNat] using ht
  · rintro rfl; decide

theorem firstWitness_eq_of_prefix_all_one (p q : ℕ) (pref rem : List ℕ)
    (hall : ∀ u ∈ pref, powMod p u q = 1) :
    firstWitness p q (pref ++ rem) = firstWitness p q rem := by
  induction pref with
  | nil => rfl
  | cons x xs ih =>
      have hx : powMod p x q = 1 := hall x (by simp)
      have hdec : decide (powMod p x q ≠ 1) = false := by simp [hx]
      rw [List.cons_append, firstWitness, List.find?_cons, hdec]
      exact ih (fun y hy => hall y (by simp [hy]))

theorem encodeNatListBin_eq_encNatPrefix_snoc_false (xs : List ℕ) :
    encodeNatListBin xs = encNatPrefix xs ++ [false] := by
  simpa [encodeNatListBin, Encoding.encodeList] using encodeNatListBin_eq_prefix_append xs []

theorem length_encNatPrefix_add (pref rem : List ℕ) :
    (encNatPrefix pref).length + (encodeNatListBin rem).length =
      (encodeNatListBin (pref ++ rem)).length := by
  rw [encodeNatListBin_eq_prefix_append, List.length_append]

theorem length_encodeNatListBin_tail_le (x : ℕ) (xs : List ℕ) :
    (encodeNatListBin xs).length ≤ (encodeNatListBin (x :: xs)).length := by
  simp only [encodeNatListBin, Encoding.encodeList, List.length_cons, List.length_append]
  omega

theorem nat_le_sq {n : ℕ} (hn : 1 ≤ n) : n ≤ n ^ 2 := by
  calc n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * n := Nat.mul_le_mul_left n hn
    _ = n ^ 2 := (sq n).symm

theorem nat_two_mul_le_sq {n : ℕ} (hn : 2 ≤ n) : 2 * n ≤ n ^ 2 := by
  calc 2 * n ≤ n * n := Nat.mul_le_mul_right n hn
    _ = n ^ 2 := (sq n).symm

theorem nat_le_cube {n : ℕ} (hn : 1 ≤ n) : n ≤ n ^ 3 := by
  calc n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * n ^ 2 := Nat.mul_le_mul_left n (Nat.pow_pos hn)
    _ = n ^ 3 := by ring

theorem nat_cube_ge8 {n : ℕ} (hn : 2 ≤ n) : 8 ≤ n ^ 3 := by
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ n ^ 3 := Nat.pow_le_pow_left hn 3

theorem nat_two_mul_sq_le_cube {n : ℕ} (hn : 2 ≤ n) : 2 * n ^ 2 ≤ n ^ 3 := by
  calc 2 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hn
    _ = n ^ 3 := by ring

theorem nat_four_mul_sq_le_pow4 {n : ℕ} (hn : 2 ≤ n) : 4 * n ^ 2 ≤ n ^ 4 := by
  have h1 : 4 ≤ n ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  calc 4 * n ^ 2 ≤ n ^ 2 * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) h1
    _ = n ^ 4 := by ring

theorem nat_eight_mul_le_pow4 {n : ℕ} (hn : 2 ≤ n) : 8 * n ≤ n ^ 4 := by
  have h1 : 8 ≤ n ^ 3 := nat_cube_ge8 hn
  calc 8 * n ≤ n ^ 3 * n := Nat.mul_le_mul_right n h1
    _ = n ^ 4 := by ring

theorem nat_pow4_ge16 {n : ℕ} (hn : 2 ≤ n) : 16 ≤ n ^ 4 := by
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ n ^ 4 := Nat.pow_le_pow_left hn 4

theorem powMod_step_bound {e b m d L : ℕ} (he : e ≤ L) (hb : b ≤ L) (hm : m ≤ L)
    (hd : d ≤ L) (hL : 2 ≤ L) :
    7000 * (e + 1) * (b + m + 1) ^ 2 + 3 * d + 600 ≤ 130000 * L ^ 3 + 600 := by
  have h1 : e + 1 ≤ 2 * L := by omega
  have h2 : b + m + 1 ≤ 3 * L := by omega
  have h3 : (b + m + 1) ^ 2 ≤ (3 * L) ^ 2 := Nat.pow_le_pow_left h2 2
  have h3' : (3 * L) ^ 2 = 9 * L ^ 2 := by ring
  have h4 : (e + 1) * (b + m + 1) ^ 2 ≤ (2 * L) * (9 * L ^ 2) := Nat.mul_le_mul h1 (h3.trans_eq h3')
  have h4' : (2 * L) * (9 * L ^ 2) = 18 * L ^ 3 := by ring
  have h5 : 7000 * ((e + 1) * (b + m + 1) ^ 2) ≤ 7000 * (18 * L ^ 3) :=
    Nat.mul_le_mul_left 7000 (h4.trans_eq h4')
  have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
  rw [Nat.mul_assoc]
  omega

theorem mulMod_step_bound {s1 s2 m d L : ℕ} (h1 : s1 ≤ L) (h2 : s2 ≤ L) (hm : m ≤ L)
    (hd : d ≤ L) (hL : 2 ≤ L) :
    350 * (s1 + s2 + m + 1) ^ 2 + 3 * d + 200 ≤ 3000 * L ^ 3 + 3 * L + 200 := by
  have hsum : s1 + s2 + m + 1 ≤ 4 * L := by omega
  have hsq : (s1 + s2 + m + 1) ^ 2 ≤ (4 * L) ^ 2 := Nat.pow_le_pow_left hsum 2
  have hsq' : (4 * L) ^ 2 = 16 * L ^ 2 := by ring
  have h350 : 350 * (s1 + s2 + m + 1) ^ 2 ≤ 350 * (16 * L ^ 2) :=
    Nat.mul_le_mul_left 350 (hsq.trans_eq hsq')
  have hcube : 2 * L ^ 2 ≤ L ^ 3 := nat_two_mul_sq_le_cube hL
  omega

theorem mulTo_step_bound {s1 s2 d L : ℕ} (h1 : s1 ≤ L) (h2 : s2 ≤ L) (hd : d ≤ L)
    (hL : 2 ≤ L) :
    80 * (s1 + 1) * (s1 + s2 + 1) + 3 * d + 80 ≤ 500 * L ^ 2 + 3 * L + 80 := by
  have ha : s1 + 1 ≤ 2 * L := by omega
  have hb : s1 + s2 + 1 ≤ 3 * L := by omega
  have hab : (s1 + 1) * (s1 + s2 + 1) ≤ (2 * L) * (3 * L) := Nat.mul_le_mul ha hb
  have hab' : (2 * L) * (3 * L) = 6 * L ^ 2 := by ring
  have h80 : 80 * ((s1 + 1) * (s1 + s2 + 1)) ≤ 80 * (6 * L ^ 2) :=
    Nat.mul_le_mul_left 80 (hab.trans_eq hab')
  rw [Nat.mul_assoc]
  omega

theorem divMod_step_bound {sn sd L : ℕ} (hn : sn ≤ L) (hd : sd ≤ L) (hL : 2 ≤ L) :
    200 * (sn + 1) * (sd + 1) + 60 ≤ 800 * L ^ 2 + 60 := by
  have ha : sn + 1 ≤ 2 * L := by omega
  have hb : sd + 1 ≤ 2 * L := by omega
  have hab : (sn + 1) * (sd + 1) ≤ (2 * L) * (2 * L) := Nat.mul_le_mul ha hb
  have hab' : (2 * L) * (2 * L) = 4 * L ^ 2 := by ring
  have h200 : 200 * ((sn + 1) * (sd + 1)) ≤ 200 * (4 * L ^ 2) :=
    Nat.mul_le_mul_left 200 (hab.trans_eq hab')
  rw [Nat.mul_assoc]
  omega

def FactorsHeadMatch (stk : Fin S → List Bool) : List ℕ → Prop
  | [] => stk sR = [] ∧ stk sFs = []
  | r :: rest => stk sR = r.bits ∧ stk sFs = encodeNatListBin rest

def TailNextMatch (stk : Fin S → List Bool) : List ℕ → Prop
  | [] => stk sRNext = [] ∧ stk sFs = []
  | z :: zs => stk sRNext = z.bits ∧ stk sFs = encodeNatListBin zs

theorem stackBits_le_add_of_fw (a b : SState) (L : ℕ)
    (hUs : (b.stacks sUs).length + (b.stacks sUsBak).length =
      (a.stacks sUs).length + (a.stacks sUsBak).length)
    (hW : (b.stacks sW).length ≤ (a.stacks sW).length + L)
    (hU : b.stacks sU = [])
    (haU : a.stacks sU = [])
    (h15 : RangeCleared 15 27 b.stacks)
    (ha15 : RangeCleared 15 27 a.stacks)
    (hoth : ∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW → k ≠ sU → k.val < 15 →
      b.stacks k = a.stacks k) :
    BitProgram.stackBits b.stacks ≤ BitProgram.stackBits a.stacks + L := by
  have heq : ∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW →
      (b.stacks k).length = (a.stacks k).length := by
    intro k h1 h2 h3
    by_cases hkU : k = sU
    · subst hkU; rw [hU, haU]
    · by_cases hk15 : k.val < 15
      · rw [hoth k h1 h2 h3 hkU hk15]
      · rw [h15 k (by omega) (Nat.le_of_lt_succ (Fin.isLt k)),
          ha15 k (by omega) (Nat.le_of_lt_succ (Fin.isLt k))]
  unfold BitProgram.stackBits
  set S1 := (Finset.univ : Finset (Fin S)).erase sUs
  set S2 := S1.erase sUsBak
  set S3 := S2.erase sW
  have hb1 := Finset.add_sum_erase Finset.univ (fun k => (b.stacks k).length) (Finset.mem_univ sUs)
  have hb2 := Finset.add_sum_erase S1 (fun k => (b.stacks k).length) (by decide : sUsBak ∈ S1)
  have hb3 := Finset.add_sum_erase S2 (fun k => (b.stacks k).length) (by decide : sW ∈ S2)
  have ha1 := Finset.add_sum_erase Finset.univ (fun k => (a.stacks k).length) (Finset.mem_univ sUs)
  have ha2 := Finset.add_sum_erase S1 (fun k => (a.stacks k).length) (by decide : sUsBak ∈ S1)
  have ha3 := Finset.add_sum_erase S2 (fun k => (a.stacks k).length) (by decide : sW ∈ S2)
  have hS3 : ∑ k ∈ S3, (b.stacks k).length = ∑ k ∈ S3, (a.stacks k).length := by
    refine Finset.sum_congr rfl fun k hk => heq k ?_ ?_ ?_
    · exact fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2).1 h
    · exact fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 h
    · exact fun h => (Finset.mem_erase.mp hk).1 h
  have hb_sum : ∑ k : Fin S, (b.stacks k).length =
      (b.stacks sUs).length + ((b.stacks sUsBak).length + ((b.stacks sW).length + ∑ k ∈ S3, (b.stacks k).length)) :=
    hb1.symm.trans (congrArg ((b.stacks sUs).length + ·)
      (hb2.symm.trans (congrArg ((b.stacks sUsBak).length + ·) hb3.symm)))
  have ha_sum : ∑ k : Fin S, (a.stacks k).length =
      (a.stacks sUs).length + ((a.stacks sUsBak).length + ((a.stacks sW).length + ∑ k ∈ S3, (a.stacks k).length)) :=
    ha1.symm.trans (congrArg ((a.stacks sUs).length + ·)
      (ha2.symm.trans (congrArg ((a.stacks sUsBak).length + ·) ha3.symm)))
  rw [hb_sum, ha_sum, hS3]; omega

theorem stackBits_data_le (stk : Fin S → List Bool) (fsLen usLen L : ℕ)
    (h0 : stk sIn = []) (h1 : stk sOut = [])
    (h2 : (stk sFs).length ≤ fsLen)
    (h34 : (stk sUs).length + (stk sUsBak).length ≤ usLen)
    (hP : (stk sP).length ≤ L) (hN : (stk sN).length ≤ L) (hAns : (stk sAns).length ≤ L)
    (hR : (stk sR).length ≤ L) (hRN : (stk sRNext).length ≤ L) (hRp : (stk sRp).length ≤ L)
    (hQ : (stk sQ).length ≤ L) (hE2 : (stk sE2).length ≤ L)
    (hW : (stk sW).length ≤ L) (hU : (stk sU).length ≤ L)
    (hclr : RangeCleared 15 27 stk) :
    BitProgram.stackBits stk ≤ fsLen + usLen + 10 * L := by
  unfold BitProgram.stackBits
  set S1 := (Finset.univ : Finset (Fin S)).erase sFs
  set S2 := S1.erase sUs
  set S3 := S2.erase sUsBak
  have hs1 := Finset.add_sum_erase Finset.univ (fun k => (stk k).length) (Finset.mem_univ sFs)
  have hs2 := Finset.add_sum_erase S1 (fun k => (stk k).length) (by decide : sUs ∈ S1)
  have hs3 := Finset.add_sum_erase S2 (fun k => (stk k).length) (by decide : sUsBak ∈ S2)
  have hlt : ∀ k ∈ S3, (stk k).length ≤ if 5 ≤ k.val ∧ k.val < 15 then L else 0 := fun k hk => by
    have hne3 : k ≠ sUsBak := (Finset.mem_erase.mp hk).1
    have hne2 : k ≠ sUs := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hne1 : k ≠ sFs := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2).1
    by_cases hband : 5 ≤ k.val ∧ k.val < 15
    · simp only [hband, ↓reduceIte]
      rcases k with ⟨kv, hkv⟩
      dsimp only at hband
      have : kv = 5 ∨ kv = 6 ∨ kv = 7 ∨ kv = 8 ∨ kv = 9 ∨
             kv = 10 ∨ kv = 11 ∨ kv = 12 ∨ kv = 13 ∨ kv = 14 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hP
      · exact hN
      · exact hAns
      · exact hR
      · exact hRN
      · exact hRp
      · exact hQ
      · exact hE2
      · exact hW
      · exact hU
    · simp only [hband, ↓reduceIte]
      by_cases h15 : 15 ≤ k.val
      · rw [hclr k h15 (Nat.le_of_lt_succ (Fin.isLt k))]; rfl
      · have : k.val = 0 ∨ k.val = 1 := by
          have hv2 : k.val ≠ 2 := fun h => hne1 (Fin.ext h)
          have hv3 : k.val ≠ 3 := fun h => hne2 (Fin.ext h)
          have hv4 : k.val ≠ 4 := fun h => hne3 (Fin.ext h)
          omega
        rcases this with hv0 | hv1
        · have : k = sIn := Fin.ext hv0
          rw [this, h0]; rfl
        · have : k = sOut := Fin.ext hv1
          rw [this, h1]; rfl
  have h10 : (∑ k : Fin S, if 5 ≤ k.val ∧ k.val < 15 then 1 else 0) = 10 := by decide
  have hLmul : ∀ k : Fin S, (if 5 ≤ k.val ∧ k.val < 15 then L else 0) =
      (if 5 ≤ k.val ∧ k.val < 15 then 1 else 0) * L := fun k => by split_ifs <;> simp
  have hS3 : ∑ k ∈ S3, (stk k).length ≤ 10 * L := by
    calc ∑ k ∈ S3, (stk k).length
        ≤ ∑ k ∈ S3, (if 5 ≤ k.val ∧ k.val < 15 then L else 0) := Finset.sum_le_sum hlt
      _ ≤ ∑ k : Fin S, (if 5 ≤ k.val ∧ k.val < 15 then L else 0) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 10 * L := by simp only [hLmul, ← Finset.sum_mul, h10]
  have hsum : ∑ k : Fin S, (stk k).length =
      (stk sFs).length + ((stk sUs).length + ((stk sUsBak).length + ∑ k ∈ S3, (stk k).length)) :=
    hs1.symm.trans (congrArg ((stk sFs).length + ·)
      (hs2.symm.trans (congrArg ((stk sUs).length + ·) hs3.symm)))
  rw [hsum]; omega

/-- 19. Witness-search command `firstWitnessCmd`: computes `firstWitness p q us` on `sW` while preserving `sUs`. -/
def firstWitnessBody : SCmd :=
  mkSeqList [
    popNatFrameBacked sUs sUsBak sU sTmp1 rFlag,
    mkIte rFlag
      (mkSeqList [
        mkAtom (.bnot rTmp1 rFound),
        mkIte rTmp1
          (mkSeqList [
            powModCmd sP sU sQ sTmp3,
            isOne sTmp3,
            mkAtom (.bnot rEq rEq),
            mkIte rEq
              (mkSeqList [copyStack sU sW sTmp1, mkAtom (.set rFound true)])
              mkSkip,
            clearStack sTmp3
          ])
          mkSkip,
        clearStack sU,
        mkAtom (.set rFlag true)
      ])
      (mkAtom (.set rFlag false))
  ]

def firstWitnessCmd : SCmd :=
  mkSeqList [
    mkAtom (.set rFound false),
    clearStack sW,
    mkAtom (.set rBit true),
    mkAtom (.push sW rBit),
    mkAtom (.set rFlag true),
    mkWhile rFlag firstWitnessBody,
    revMove sUsBak sUs
  ]

theorem firstWitnessBody_eval {p q : ℕ} (hp2 : 2 ≤ p) (hq : q < p)
    (us pref rem : List ℕ) (hsplit : pref ++ rem = us) (w : ℕ) (hw : w < p)
    (hrem : ∀ u ∈ rem, u < p)
    (a : SState)
    (hUs : a.stacks sUs = encodeNatListBin rem)
    (hBak : a.stacks sUsBak = (encNatPrefix pref).reverse)
    (hP : a.stacks sP = p.bits) (hQ : a.stacks sQ = q.bits)
    (hW : a.stacks sW = w.bits) (hU : a.stacks sU = [])
    (hclr : RangeCleared 15 27 a.stacks)
    (hfnd_inv : if a.regs rFound then w = firstWitness p q us
                else w = 1 ∧ ∀ u ∈ pref, powMod p u q = 1) :
    let L := bitLen p + 1
    ∃ n b w', StructuredCalls.Eval firstWitnessBody n a b ∧
      n ≤ 140000 * L ^ 3 + 1000 ∧
      b.regs rFlag = !rem.isEmpty ∧
      (match rem with
        | [] => b.stacks sUs = [] ∧ b.stacks sUsBak = (encodeNatListBin us).reverse ∧
                b.stacks sW = w.bits ∧ b.regs rFound = a.regs rFound ∧
                (if b.regs rFound then w = firstWitness p q us
                 else w = 1 ∧ ∀ u ∈ us, powMod p u q = 1)
        | u :: rest =>
            b.stacks sUs = encodeNatListBin rest ∧
            b.stacks sUsBak = (encNatPrefix (pref ++ [u])).reverse ∧
            w' < p ∧ b.stacks sW = w'.bits ∧
            (if b.regs rFound then w' = firstWitness p q us
             else w' = 1 ∧ ∀ x ∈ pref ++ [u], powMod p x q = 1)) ∧
      b.stacks sU = [] ∧ RangeCleared 15 27 b.stacks ∧
      (∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW → k ≠ sU → k.val < 15 →
        b.stacks k = a.stacks k) ∧
      b.regs rHasR = a.regs rHasR ∧ b.regs rHasNext = a.regs rHasNext := by
  let L := bitLen p + 1
  have hL : 2 ≤ L := by
    have : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  have hP_len : p.bits.length ≤ L := prime_bits_length_le hp2
  have hQ_len : q.bits.length ≤ L := lt_prime_bits_length_le hq
  have hW_len : w.bits.length ≤ L := lt_prime_bits_length_le hw
  obtain ⟨n₁, b₁, e₁, hn₁, h1s, h1b, h1U, h1t1, h1o, h1f, h1_9, h1_11, h1_12⟩ :=
    popNatFrameBacked_eval (by decide : sUs ≠ sUsBak) (by decide : sUs ≠ sU)
      (by decide : sUs ≠ sTmp1) (by decide : sUsBak ≠ sU) (by decide : sUsBak ≠ sTmp1)
      (by decide : sU ≠ sTmp1) rFlag (by decide) (Or.inr (Or.inr rfl)) rem a hUs
      (hclr sTmp1 (by decide) (by decide))
  have h1_rFound : b₁.regs rFound = a.regs rFound := h1_9 (by decide)
  have h1_rHasR : b₁.regs rHasR = a.regs rHasR := h1_11 (by decide)
  have h1_rHasNext : b₁.regs rHasNext = a.regs rHasNext := h1_12 (by decide)
  have h1clr : RangeCleared 15 27 b₁.stacks := by
    intro k hk1 hk2
    by_cases hkt1 : k = sTmp1
    · subst hkt1; exact h1t1
    · rw [h1o k (fin_ne_of_lt_ge 15 (by decide) hk1).symm
          (fin_ne_of_lt_ge 15 (by decide) hk1).symm
          (fin_ne_of_lt_ge 15 (by decide) hk1).symm hkt1]
      exact hclr k hk1 hk2
  cases rem with
  | nil =>
      simp only [List.isEmpty_nil, Bool.not_true] at hn₁ h1f h1s h1b h1U
      rw [List.append_nil] at hsplit; subst hsplit
      let b₂ : SState := ⟨Function.update b₁.regs rFlag false, b₁.stacks⟩
      have e₂ := eval_set b₁ rFlag false
      have h2f : b₂.regs rFound = a.regs rFound := by
        dsimp only [b₂]; rw [Function.update_of_ne (by decide : rFound ≠ rFlag), h1_rFound]
      refine ⟨_, b₂, w, .seq e₁ (.ite_false h1f e₂), ?_, by simp [b₂], ?_,
        h1U, h1clr, ?_, ?_, ?_⟩
      · have hsu0 : (a.stacks sU).length = 0 := by rw [hU]; rfl
        rw [hsu0] at hn₁; omega
      · refine ⟨h1s, ?_, ?_, h2f, ?_⟩
        · dsimp only [b₂]; rw [h1b, hBak, encodeNatListBin_eq_encNatPrefix_snoc_false]
          simp [List.reverse_append]
        · dsimp only [b₂]; rw [h1o sW (by decide) (by decide) (by decide) (by decide), hW]
        · simpa [h2f] using hfnd_inv
      · intro k hku hkb _ hkU hk15
        dsimp only [b₂]; exact h1o k hku hkb hkU (fin_ne_of_lt_ge 15 hk15 (by decide))
      · dsimp only [b₂]; rw [Function.update_of_ne (by decide : rHasR ≠ rFlag), h1_rHasR]
      · dsimp only [b₂]; rw [Function.update_of_ne (by decide : rHasNext ≠ rFlag), h1_rHasNext]
  | cons u rest =>
      simp only [List.isEmpty_cons, Bool.not_false] at hn₁ h1f h1s h1b h1U
      have hu_lt : u < p := hrem u (by simp)
      have hu_len : u.bits.length ≤ L := lt_prime_bits_length_le hu_lt
      have hcw_u : (countWord u).length ≤ L :=
        (countWord_length_le u).trans (max_le (by omega) hu_len)
      have h1P : b₁.stacks sP = p.bits :=
        (h1o sP (by decide) (by decide) (by decide) (by decide)).trans hP
      have h1Q : b₁.stacks sQ = q.bits :=
        (h1o sQ (by decide) (by decide) (by decide) (by decide)).trans hQ
      have h1W : b₁.stacks sW = w.bits :=
        (h1o sW (by decide) (by decide) (by decide) (by decide)).trans hW
      have h1_keep15 : ∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW → k ≠ sU → k.val < 15 →
          b₁.stacks k = a.stacks k := fun k hku hkb _ hkU hk15 =>
        h1o k hku hkb hkU (fin_ne_of_lt_ge 15 hk15 (by decide))
      let b₂ : SState := ⟨Function.update b₁.regs rTmp1 (!(b₁.regs rFound)), b₁.stacks⟩
      have e₂ := eval_bnot b₁ rTmp1 rFound
      have h2fnd : b₂.regs rFound = a.regs rFound := by
        dsimp only [b₂]; rw [Function.update_of_ne (by decide : rFound ≠ rTmp1), h1_rFound]
      have h2_hasR : b₂.regs rHasR = a.regs rHasR := by
        dsimp only [b₂]; rw [Function.update_of_ne (by decide : rHasR ≠ rTmp1), h1_rHasR]
      have h2_hasNext : b₂.regs rHasNext = a.regs rHasNext := by
        dsimp only [b₂]; rw [Function.update_of_ne (by decide : rHasNext ≠ rTmp1), h1_rHasNext]
      have h1_bak' : b₁.stacks sUsBak = (encNatPrefix (pref ++ [u])).reverse := by
        rw [h1b, hBak]
        have happ : encNatPrefix (pref ++ [u]) = encNatPrefix pref ++ (true :: Encoding.frame (countWord u)) := by
          rw [encNatPrefix_append]; simp [encNatPrefix]
        rw [happ, List.reverse_append]
      cases hfnd_case : a.regs rFound with
      | true =>
          have ht2 : b₂.regs rTmp1 = false := by
            dsimp only [b₂]; rw [Function.update_self, h1_rFound, hfnd_case]; rfl
          have hfnd_inv' : w = firstWitness p q us := by
            simpa [hfnd_case] using hfnd_inv
          obtain ⟨n₅, b₅, e₅, hn₅, h5U, h5o, h5reg⟩ := clearStack_eval sU b₂
          let b₆ : SState := ⟨Function.update b₅.regs rFlag true, b₅.stacks⟩
          have e₆ := eval_set b₅ rFlag true
          refine ⟨_, b₆, w, .seq e₁ (.ite_true h1f (.seq e₂ (.seq (.ite_false ht2 (.base (.skip b₂))) (.seq e₅ e₆)))),
            ?_, by simp [b₆], ?_, h5U, ?_, ?_, ?_, ?_⟩
          · have hsu0 : (a.stacks sU).length = 0 := by rw [hU]; rfl
            rw [hsu0] at hn₁
            have hb2U : (b₂.stacks sU).length = u.bits.length := by rw [h1U]
            rw [hb2U] at hn₅
            have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
            dsimp only [L] at *
            omega
          · refine ⟨?_, ?_, hw, ?_, ?_⟩
            · dsimp only [b₆]; rw [h5o sUs (by decide)]; exact h1s
            · dsimp only [b₆]; rw [h5o sUsBak (by decide)]; exact h1_bak'
            · dsimp only [b₆]; rw [h5o sW (by decide)]; exact h1W
            · have hf6 : b₆.regs rFound = true := by
                dsimp only [b₆]; rw [Function.update_of_ne (by decide : rFound ≠ rFlag), ← h5reg.1, h2fnd, hfnd_case]
              simp [hf6, hfnd_inv']
          · intro k hk1 hk2
            dsimp only [b₆]; rw [h5o k (fin_ne_of_lt_ge 15 (by decide) hk1).symm]
            exact h1clr k hk1 hk2
          · intro k hku hkb hkw hkU hk15
            dsimp only [b₆]; rw [h5o k hkU]
            exact h1_keep15 k hku hkb hkw hkU hk15
          · dsimp only [b₆]; rw [Function.update_of_ne (by decide : rHasR ≠ rFlag), ← h5reg.2.1, h2_hasR]
          · dsimp only [b₆]; rw [Function.update_of_ne (by decide : rHasNext ≠ rFlag), ← h5reg.2.2, h2_hasNext]
      | false =>
          have ht2 : b₂.regs rTmp1 = true := by
            dsimp only [b₂]; rw [Function.update_self, h1_rFound, hfnd_case]; rfl
          obtain ⟨hw1, hpref_all⟩ : w = 1 ∧ ∀ x ∈ pref, powMod p x q = 1 := by
            simpa [hfnd_case] using hfnd_inv
          obtain ⟨n₃, b₃, e₃, hn₃, h3t3, h3ge15, h3lt15, h3reg⟩ :=
            powModCmd_eval (by decide : sP.val < 15) (by decide : sU.val < 15)
              (by decide : sQ.val < 15) (Or.inr rfl) b₂
              (by rw [h1P, toNat_bits]; exact hp2) h1clr
          have h3t3_val : b₃.stacks sTmp3 = (powMod p u q).bits := by
            rw [h3t3]; dsimp only [b₂]; rw [h1P, h1U, h1Q, toNat_bits, toNat_bits, toNat_bits]
          have hpow_lt : powMod p u q < p := by
            rw [powMod_eq]; exact Nat.mod_lt _ (by omega)
          have hpow_len : (b₃.stacks sTmp3).length ≤ L := by
            rw [h3t3_val]; exact lt_prime_bits_length_le hpow_lt
          obtain ⟨n₄, b₄, e₄, hn₄, h4stk, h4eq, h4reg⟩ := isOne_eval sTmp3 b₃
          have h4eq_val : b₄.regs rEq = decide (powMod p u q = 1) := by
            rw [h4eq, h3t3_val, decide_eq_decide]
            exact bits_eq_one_iff _
          let b₅ : SState := ⟨Function.update b₄.regs rEq (!(b₄.regs rEq)), b₄.stacks⟩
          have e₅ := eval_bnot b₄ rEq rEq
          have h5eq : b₅.regs rEq = decide (powMod p u q ≠ 1) := by
            dsimp only [b₅]; rw [Function.update_self, h4eq_val]; cases hpow : decide (powMod p u q = 1) <;> simp_all
          have h5reg : RegPreserved b₂ b₅ :=
            regPreserved_trans h3reg (regPreserved_trans h4reg
              (regPreserved_update (!(b₄.regs rEq)) b₄.stacks (by decide) (by decide) (by decide)))
          have h5_fnd : b₅.regs rFound = false := (h5reg.1).symm.trans (h2fnd.trans hfnd_case)
          have h5_hasR : b₅.regs rHasR = a.regs rHasR := (h5reg.2.1).symm.trans h2_hasR
          have h5_hasNext : b₅.regs rHasNext = a.regs rHasNext := (h5reg.2.2).symm.trans h2_hasNext
          have h5lt15 : ∀ k : Fin S, k.val < 15 → b₅.stacks k = b₂.stacks k := fun k hk => by
            dsimp only [b₅]; rw [h4stk]; exact h3lt15 k hk (fin_ne_of_lt_ge 15 hk (by decide))
          have h5ge15 : ∀ k : Fin S, 15 ≤ k.val → k ≠ sTmp3 → b₅.stacks k = [] := fun k hk hne => by
            dsimp only [b₅]; rw [h4stk]; exact h3ge15 k hk hne
          have h5t3 : (b₅.stacks sTmp3).length ≤ L := by dsimp only [b₅]; rw [h4stk]; exact hpow_len
          have h5U : b₅.stacks sU = u.bits := (h5lt15 sU (by decide)).trans h1U
          have h5W : b₅.stacks sW = w.bits := (h5lt15 sW (by decide)).trans h1W
          have hn3_bd : n₃ ≤ 130000 * L ^ 3 + 600 := by
            dsimp only [b₂] at hn₃
            rw [h1Q, h1U, h1P] at hn₃
            have hb3_t3 : (b₂.stacks sTmp3).length = 0 := by rw [h1clr sTmp3 (by decide) (by decide)]; rfl
            rw [hb3_t3] at hn₃
            exact hn₃.trans (powMod_step_bound hQ_len hu_len hP_len (Nat.zero_le L) hL)
          by_cases hpow1 : powMod p u q = 1
          · have ht5 : b₅.regs rEq = false := by rw [h5eq]; simp [hpow1]
            obtain ⟨n₆, b₆, e₆, hn₆, h6t3, h6o, h6reg⟩ := clearStack_eval sTmp3 b₅
            obtain ⟨n₇, b₇, e₇, hn₇, h7U, h7o, h7reg⟩ := clearStack_eval sU b₆
            let b₈ : SState := ⟨Function.update b₇.regs rFlag true, b₇.stacks⟩
            have e₈ := eval_set b₇ rFlag true
            refine ⟨_, b₈, w,
              .seq e₁ (.ite_true h1f (.seq e₂ (.seq (.ite_true ht2
                (.seq e₃ (.seq e₄ (.seq e₅ (.seq (.ite_false ht5 (.base (.skip b₅))) e₆))))) (.seq e₇ e₈)))),
              ?_, by simp [b₈], ?_, ?_, ?_, ?_, ?_, ?_⟩
            · have hsu0 : (a.stacks sU).length = 0 := by rw [hU]; rfl
              rw [hsu0] at hn₁
              have h6U_len : (b₆.stacks sU).length = u.bits.length := by rw [h6o sU (by decide), h5U]
              rw [h6U_len] at hn₇
              have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
              dsimp only [L] at *
              omega
            · refine ⟨?_, ?_, hw, ?_, ?_⟩
              · dsimp only [b₈]; rw [h7o sUs (by decide), h6o sUs (by decide), h5lt15 sUs (by decide)]; exact h1s
              · dsimp only [b₈]; rw [h7o sUsBak (by decide), h6o sUsBak (by decide), h5lt15 sUsBak (by decide)]; exact h1_bak'
              · dsimp only [b₈]; rw [h7o sW (by decide), h6o sW (by decide), h5W]
              · have hf8 : b₈.regs rFound = false := by
                  dsimp only [b₈]; rw [Function.update_of_ne (by decide : rFound ≠ rFlag), ← h7reg.1, ← h6reg.1, h5_fnd]
                simp only [hf8, Bool.false_eq_true, ↓reduceIte]
                refine ⟨hw1, fun x hx => ?_⟩
                simp only [List.mem_append, List.mem_singleton] at hx
                rcases hx with hx | rfl
                · exact hpref_all x hx
                · exact hpow1
            · dsimp only [b₈]; exact h7U
            · intro k hk1 hk2
              dsimp only [b₈]; rw [h7o k (fin_ne_of_lt_ge 15 (by decide) hk1).symm]
              by_cases hkt3 : k = sTmp3
              · subst hkt3; exact h6t3
              · rw [h6o k hkt3]; exact h5ge15 k hk1 hkt3
            · intro k hku hkb hkw hkU hk15
              dsimp only [b₈]; rw [h7o k hkU, h6o k (fin_ne_of_lt_ge 15 hk15 (by decide)), h5lt15 k hk15]
              exact h1_keep15 k hku hkb hkw hkU hk15
            · dsimp only [b₈]; rw [Function.update_of_ne (by decide : rHasR ≠ rFlag), ← h7reg.2.1, ← h6reg.2.1, h5_hasR]
            · dsimp only [b₈]; rw [Function.update_of_ne (by decide : rHasNext ≠ rFlag), ← h7reg.2.2, ← h6reg.2.2, h5_hasNext]
          · have ht5 : b₅.regs rEq = true := by rw [h5eq]; simp [hpow1]
            have h5_t1 : b₅.stacks sTmp1 = [] := h5ge15 sTmp1 (by decide) (by decide)
            obtain ⟨nc, bc, ec, hnc, hcU, hcW, hct1, hco, hcreg⟩ :=
              copyStack_eval (by decide : sU ≠ sW) (by decide : sU ≠ sTmp1) (by decide : sW ≠ sTmp1) b₅ h5_t1
            let bc1 : SState := ⟨Function.update bc.regs rFound true, bc.stacks⟩
            have ec1 := eval_set bc rFound true
            obtain ⟨n₆, b₆, e₆, hn₆, h6t3, h6o, h6reg⟩ := clearStack_eval sTmp3 bc1
            obtain ⟨n₇, b₇, e₇, hn₇, h7U, h7o, h7reg⟩ := clearStack_eval sU b₆
            let b₈ : SState := ⟨Function.update b₇.regs rFlag true, b₇.stacks⟩
            have e₈ := eval_set b₇ rFlag true
            have hfw_u : u = firstWitness p q us := by
              rw [← hsplit, firstWitness_eq_of_prefix_all_one p q pref (u :: rest) hpref_all]
              simp [firstWitness, hpow1]
            refine ⟨_, b₈, u,
              .seq e₁ (.ite_true h1f (.seq e₂ (.seq (.ite_true ht2
                (.seq e₃ (.seq e₄ (.seq e₅ (.seq (.ite_true ht5 (.seq ec ec1)) e₆))))) (.seq e₇ e₈)))),
              ?_, by simp [b₈], ?_, ?_, ?_, ?_, ?_, ?_⟩
            · have hsu0 : (a.stacks sU).length = 0 := by rw [hU]; rfl
              rw [hsu0] at hn₁
              rw [h5W, h5U] at hnc
              have hbc1_t3 : (bc1.stacks sTmp3).length ≤ L := by
                dsimp only [bc1]; rw [hco sTmp3 (by decide) (by decide)]; exact h5t3
              have hb6_U : (b₆.stacks sU).length = u.bits.length := by
                rw [h6o sU (by decide)]; dsimp only [bc1]; rw [hcU, h5U]
              rw [hb6_U] at hn₇
              have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
              dsimp only [L] at *
              omega
            · refine ⟨?_, ?_, hu_lt, ?_, ?_⟩
              · dsimp only [b₈]; rw [h7o sUs (by decide), h6o sUs (by decide)]
                dsimp only [bc1]; rw [hco sUs (by decide) (by decide), h5lt15 sUs (by decide)]; exact h1s
              · dsimp only [b₈]; rw [h7o sUsBak (by decide), h6o sUsBak (by decide)]
                dsimp only [bc1]; rw [hco sUsBak (by decide) (by decide), h5lt15 sUsBak (by decide)]; exact h1_bak'
              · dsimp only [b₈]; rw [h7o sW (by decide), h6o sW (by decide)]
                dsimp only [bc1]; rw [hcW, h5U]
              · have hf8 : b₈.regs rFound = true := by
                  dsimp only [b₈]; rw [Function.update_of_ne (by decide : rFound ≠ rFlag), ← h7reg.1, ← h6reg.1]
                  dsimp only [bc1]; rw [Function.update_self]
                simp [hf8, hfw_u]
            · dsimp only [b₈]; exact h7U
            · intro k hk1 hk2
              dsimp only [b₈]; rw [h7o k (fin_ne_of_lt_ge 15 (by decide) hk1).symm]
              by_cases hkt3 : k = sTmp3
              · subst hkt3; exact h6t3
              · rw [h6o k hkt3]; dsimp only [bc1]
                by_cases hkt1 : k = sTmp1
                · subst hkt1; exact hct1
                · rw [hco k (fin_ne_of_lt_ge 15 (by decide) hk1).symm hkt1]
                  exact h5ge15 k hk1 hkt3
            · intro k hku hkb hkw hkU hk15
              dsimp only [b₈]; rw [h7o k hkU, h6o k (fin_ne_of_lt_ge 15 hk15 (by decide))]
              dsimp only [bc1]; rw [hco k hkw (fin_ne_of_lt_ge 15 hk15 (by decide)), h5lt15 k hk15]
              exact h1_keep15 k hku hkb hkw hkU hk15
            · dsimp only [b₈]; rw [Function.update_of_ne (by decide : rHasR ≠ rFlag), ← h7reg.2.1, ← h6reg.2.1]
              dsimp only [bc1]; rw [Function.update_of_ne (by decide : rHasR ≠ rFound), ← hcreg.2.1, h5_hasR]
            · dsimp only [b₈]; rw [Function.update_of_ne (by decide : rHasNext ≠ rFlag), ← h7reg.2.2, ← h6reg.2.2]
              dsimp only [bc1]; rw [Function.update_of_ne (by decide : rHasNext ≠ rFound), ← hcreg.2.2, h5_hasNext]

theorem firstWitnessLoop_eval {p q : ℕ} (hp2 : 2 ≤ p) (hq : q < p)
    (us : List ℕ) (hus : ∀ u ∈ us, u < p)
    (pref rem : List ℕ) (hsplit : pref ++ rem = us) (w : ℕ) (hw : w < p)
    (x0 : SState) (hf : x0.regs rFlag = true)
    (hUs : x0.stacks sUs = encodeNatListBin rem)
    (hBak : x0.stacks sUsBak = (encNatPrefix pref).reverse)
    (hP : x0.stacks sP = p.bits) (hQ : x0.stacks sQ = q.bits)
    (hW : x0.stacks sW = w.bits) (hU : x0.stacks sU = [])
    (hclr : RangeCleared 15 27 x0.stacks)
    (hfnd_inv : if x0.regs rFound then w = firstWitness p q us
                else w = 1 ∧ ∀ u ∈ pref, powMod p u q = 1) :
    let L := bitLen p + 1
    ∃ n b, StructuredCalls.Eval (mkWhile rFlag firstWitnessBody) n x0 b ∧
      n ≤ (rem.length + 1) * (140000 * L ^ 3 + 1500) + 13 ∧
      b.stacks sUs = [] ∧
      b.stacks sUsBak = (encodeNatListBin us).reverse ∧
      b.stacks sW = (firstWitness p q us).bits ∧
      b.stacks sU = [] ∧ RangeCleared 15 27 b.stacks ∧
      (∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW → k ≠ sU → k.val < 15 →
        b.stacks k = x0.stacks k) ∧
      b.regs rHasR = x0.regs rHasR ∧ b.regs rHasNext = x0.regs rHasNext := by
  induction rem generalizing pref w x0 with
  | nil =>
      obtain ⟨n₁, b₁, w₁, e₁, hn₁, h1f, ⟨h1s, h1b, h1W, h1_fnd, hfnd1⟩, h1U, h1clr, h1o, h1_11, h1_12⟩ :=
        firstWitnessBody_eval hp2 hq us pref [] hsplit w hw (fun _ h => nomatch h)
          x0 hUs hBak hP hQ hW hU hclr hfnd_inv
      simp only [List.isEmpty_nil, Bool.not_true] at h1f
      have hw_final : w = firstWitness p q us := by
        cases hfc : b₁.regs rFound with
        | true => simpa [hfc] using hfnd1
        | false =>
            have hfnd1' : w = 1 ∧ ∀ u ∈ us, powMod p u q = 1 := by simpa [hfc] using hfnd1
            have hall := hfnd1'.2
            have hw1 := hfnd1'.1
            rw [hw1]
            symm
            have : us ++ [] = us := List.append_nil us
            rw [← this, firstWitness_eq_of_prefix_all_one p q us [] hall]
            rfl
      refine ⟨n₁ + 1 + 1, b₁, .while_true hf e₁ (.while_false h1f), ?_, h1s, h1b,
        by rw [h1W, hw_final], h1U, h1clr, h1o, h1_11, h1_12⟩
      simp only [List.length_nil, zero_add, one_mul]
      omega
  | cons u rest ih =>
      have hrem_mem : ∀ z ∈ u :: rest, z < p := fun z hz => hus z (by rw [← hsplit]; simp [hz])
      obtain ⟨n₁, b₁, w', e₁, hn₁, h1f, ⟨h1s, h1b, hw', h1W, hfnd1⟩, h1U, h1clr, h1o, h1_11, h1_12⟩ :=
        firstWitnessBody_eval hp2 hq us pref (u :: rest) hsplit w hw hrem_mem
          x0 hUs hBak hP hQ hW hU hclr hfnd_inv
      simp only [List.isEmpty_cons, Bool.not_false] at h1f
      have hsplit' : (pref ++ [u]) ++ rest = us := by simp [List.append_assoc, hsplit]
      have h1P : b₁.stacks sP = p.bits :=
        (h1o sP (by decide) (by decide) (by decide) (by decide) (by decide)).trans hP
      have h1Q : b₁.stacks sQ = q.bits :=
        (h1o sQ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hQ
      obtain ⟨n₂, b₂, e₂, hn₂, h2s, h2b, h2W, h2U, h2clr, h2o, h2_11, h2_12⟩ :=
        ih (pref ++ [u]) hsplit' w' hw' b₁ h1f h1s h1b h1P h1Q h1W h1U h1clr hfnd1
      refine ⟨n₁ + n₂ + 1, b₂, .while_true hf e₁ e₂, ?_, h2s, h2b, h2W, h2U, h2clr, ?_,
        h2_11.trans h1_11, h2_12.trans h1_12⟩
      · simp only [List.length_cons] at hn₂ ⊢
        have hmul : (rest.length + 1 + 1) * (140000 * (bitLen p + 1) ^ 3 + 1500) =
            (rest.length + 1) * (140000 * (bitLen p + 1) ^ 3 + 1500) + (140000 * (bitLen p + 1) ^ 3 + 1500) := by ring
        omega
      · intro k hku hkb hkw hkU hk15
        rw [h2o k hku hkb hkw hkU hk15, h1o k hku hkb hkw hkU hk15]

theorem firstWitness_spec {p q B : ℕ} (hp2 : 2 ≤ p) (hq : q < p)
    (us : List ℕ) (hus : ∀ u ∈ us, u < p)
    (a : SState)
    (hP : a.stacks sP = p.bits) (hQ : a.stacks sQ = q.bits)
    (hUs : a.stacks sUs = encodeNatListBin us)
    (hBak : a.stacks sUsBak = []) (hW : a.stacks sW = []) (hU : a.stacks sU = [])
    (hclr : RangeCleared 15 27 a.stacks)
    (hB : BitProgram.stackBits a.stacks + 150000 * (bitLen p + 1) ^ 3 + 5000 ≤ B) :
    let L := bitLen p + 1
    ∃ n b, Spec sIn sOut firstWitnessCmd a b n B ∧
      n ≤ (us.length + 1) * (140000 * L ^ 3 + 1500) + 4 * (encodeNatListBin us).length + 30 ∧
      b.stacks sUs = encodeNatListBin us ∧
      b.stacks sUsBak = [] ∧ b.stacks sW = (firstWitness p q us).bits ∧ b.stacks sU = [] ∧
      RangeCleared 15 27 b.stacks ∧
      (∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW → k ≠ sU → k.val < 15 →
        b.stacks k = a.stacks k) ∧
      b.regs rHasR = a.regs rHasR ∧ b.regs rHasNext = a.regs rHasNext := by
  let L := bitLen p + 1
  have hL : 2 ≤ L := by
    have : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  -- Prologue: set rFound false; clearStack sW; set rBit true; push sW rBit; set rFlag true
  let a₁ : SState := ⟨Function.update a.regs rFound false, a.stacks⟩
  have ea₁ := eval_set a rFound false
  obtain ⟨ncw, a₂, e₂, hncw, h2W, h2o, h2reg⟩ := clearStack_eval sW a₁
  let a₃ : SState := ⟨Function.update a₂.regs rBit true, a₂.stacks⟩
  have ea₃ := eval_set a₂ rBit true
  let a₄ : SState := ⟨a₃.regs, Function.update a₃.stacks sW (true :: a₃.stacks sW)⟩
  have ea₄ : StructuredCalls.Eval (mkAtom (.push sW rBit)) 1 a₃ a₄ := by
    simpa [a₃, a₄] using eval_push a₃ sW rBit
  let a₅ : SState := ⟨Function.update a₄.regs rFlag true, a₄.stacks⟩
  have ea₅ := eval_set a₄ rFlag true
  have ha5_keep : ∀ k : Fin S, k ≠ sW → a₅.stacks k = a.stacks k := fun k hk => by
    dsimp only [a₅, a₄, a₃]; rw [Function.update_of_ne hk, h2o k hk]
  have ha5_W : a₅.stacks sW = (1 : ℕ).bits := by
    dsimp only [a₅, a₄, a₃]; rw [Function.update_self, h2W]; decide
  have ha5_bits : BitProgram.stackBits a₅.stacks ≤ BitProgram.stackBits a.stacks + 1 := by
    have hu := BitProgram.stackBits_update a₃.stacks sW [true]
    have ha3_W : a₃.stacks sW = [] := by dsimp only [a₃]; exact h2W
    have ha3_eq : BitProgram.stackBits a₃.stacks = BitProgram.stackBits a.stacks := by
      have : a₃.stacks = a.stacks := by
        funext k
        by_cases hk : k = sW
        · subst hk; rw [ha3_W, hW]
        · dsimp only [a₃]; exact h2o k hk
      rw [this]
    rw [ha3_W, ha3_eq] at hu
    dsimp only [a₅, a₄]; simp only [a₃, h2W, List.length_nil, List.length_singleton] at hu ⊢; omega
  have hnp_bd : 1 + (ncw + (1 + (1 + 1))) ≤ 10 := by
    have : (a₁.stacks sW).length = 0 := by simp [a₁, hW]
    rw [this] at hncw; omega
  have ha2_eq : a₂.stacks = a.stacks := by
    funext k
    by_cases hk : k = sW
    · subst hk; rw [h2W, hW]
    · exact h2o k hk
  have sp₁ : Spec sIn sOut (mkAtom (.set rFound false)) a a₁ 1 B :=
    Spec.of_eval_local ea₁ (by omega)
  have sp₂ : Spec sIn sOut (clearStack sW) a₁ a₂ ncw B :=
    Spec.of_eval_local e₂ (by change BitProgram.stackBits a.stacks + ncw ≤ B; omega)
  have sp₃ : Spec sIn sOut (mkAtom (.set rBit true)) a₂ a₃ 1 B :=
    Spec.of_eval_local ea₃ (by rw [ha2_eq]; omega)
  have sp₄ : Spec sIn sOut (mkAtom (.push sW rBit)) a₃ a₄ 1 B :=
    Spec.of_eval_local ea₄ (by change BitProgram.stackBits a₂.stacks + 1 ≤ B; rw [ha2_eq]; omega)
  have sp₅ : Spec sIn sOut (mkAtom (.set rFlag true)) a₄ a₅ 1 B :=
    Spec.of_eval_local ea₅ (by change BitProgram.stackBits a₅.stacks + 1 ≤ B; omega)
  -- Loop body Spec via `Spec.while`
  have h5Us : a₅.stacks sUs = encodeNatListBin us := ha5_keep sUs (by decide) ▸ hUs
  have h5Bak : a₅.stacks sUsBak = (encNatPrefix ([] : List ℕ)).reverse := by
    rw [ha5_keep sUsBak (by decide), hBak]; rfl
  have h5P : a₅.stacks sP = p.bits := (ha5_keep sP (by decide)).trans hP
  have h5Q : a₅.stacks sQ = q.bits := (ha5_keep sQ (by decide)).trans hQ
  have h5U : a₅.stacks sU = [] := (ha5_keep sU (by decide)).trans hU
  have h5clr : RangeCleared 15 27 a₅.stacks := fun k hk1 hk2 =>
    (ha5_keep k (fin_ne_of_lt_ge 15 (by decide) hk1).symm).trans (hclr k hk1 hk2)
  have h5flag : a₅.regs rFlag = true := by dsimp only [a₅]; rw [Function.update_self]
  have h5fnd : a₅.regs rFound = false := by
    dsimp only [a₅]; rw [Function.update_of_ne (by decide : rFound ≠ rFlag)]
    dsimp only [a₄, a₃]; rw [Function.update_of_ne (by decide : rFound ≠ rBit), ← h2reg.1]
    dsimp only [a₁]; rw [Function.update_self]
  have h5hasR : a₅.regs rHasR = a.regs rHasR := by
    dsimp only [a₅]; rw [Function.update_of_ne (by decide : rHasR ≠ rFlag)]
    dsimp only [a₄, a₃]; rw [Function.update_of_ne (by decide : rHasR ≠ rBit), ← h2reg.2.1]
    dsimp only [a₁]; rw [Function.update_of_ne (by decide : rHasR ≠ rFound)]
  have h5hasNext : a₅.regs rHasNext = a.regs rHasNext := by
    dsimp only [a₅]; rw [Function.update_of_ne (by decide : rHasNext ≠ rFlag)]
    dsimp only [a₄, a₃]; rw [Function.update_of_ne (by decide : rHasNext ≠ rBit), ← h2reg.2.2]
    dsimp only [a₁]; rw [Function.update_of_ne (by decide : rHasNext ≠ rFound)]
  obtain ⟨nl, b_loop, e_loop, hnl, hlUs, hlBak, hlW, hlU, hlclr, hloth, hl_hasR, hl_hasNext⟩ :=
    firstWitnessLoop_eval hp2 hq us hus [] us rfl 1 (by omega) a₅ h5flag h5Us h5Bak h5P h5Q ha5_W h5U h5clr
      (by simp [h5fnd])
  let I : SState → Prop := fun x =>
    ∃ (pref rem : List ℕ) (w : ℕ),
      pref ++ rem = us ∧
      (if x.regs rFlag then
         x.stacks sUs = encodeNatListBin rem ∧ x.stacks sUsBak = (encNatPrefix pref).reverse
       else
         rem = [] ∧ x.stacks sUs = [] ∧ x.stacks sUsBak = (encodeNatListBin us).reverse) ∧
      (if x.regs rFound then w = firstWitness p q us else w = 1 ∧ ∀ u ∈ pref, powMod p u q = 1) ∧
      w < p ∧
      x.stacks sP = p.bits ∧ x.stacks sQ = q.bits ∧
      x.stacks sW = w.bits ∧ x.stacks sU = [] ∧
      RangeCleared 15 27 x.stacks ∧
      (∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW → k ≠ sU → k.val < 15 →
        x.stacks k = a.stacks k) ∧
      x.regs rHasR = a.regs rHasR ∧ x.regs rHasNext = a.regs rHasNext
  have hI_bits : ∀ x, I x → BitProgram.stackBits x.stacks ≤ BitProgram.stackBits a.stacks + L := by
    intro x ⟨pref, rem, w, hsp, hflags, _, hw_lt, _, _, hxW, hxU, hxclr, hxoth, _, _⟩
    refine stackBits_le_add_of_fw a x L ?_ ?_ hxU hU hxclr hclr hxoth
    · cases hfl : x.regs rFlag with
      | true =>
          simp only [hfl, ↓reduceIte] at hflags
          rw [hflags.1, hflags.2, List.length_reverse, add_comm, length_encNatPrefix_add, hsp, hUs, hBak]
          simp
      | false =>
          simp only [hfl, Bool.false_eq_true, ↓reduceIte] at hflags
          rw [hflags.2.1, hflags.2.2, hUs, hBak]
          simp
    · rw [hxW, hW]; simp only [List.length_nil, zero_add]; exact lt_prime_bits_length_le hw_lt
  have hinit : ∀ x, I x → ∀ i, (x.stacks i).length ≤ B := fun x hx i => by
    have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
    dsimp only [L] at *
    exact (stackLength_le_stackBits x.stacks i).trans ((hI_bits x hx).trans (by omega))
  have hstep : ∀ x, I x → x.regs rFlag = true →
      ∃ n y, Spec sIn sOut firstWitnessBody x y n B ∧ I y := by
    intro x hx hxf
    have hx_bits := hI_bits x hx
    rcases hx with ⟨pref, rem, w, hsp, hflags, hfnd, hw_lt, hxP, hxQ, hxW, hxU, hxclr, hxoth, hx_hasR, hx_hasNext⟩
    simp only [hxf, ↓reduceIte] at hflags
    have hrem_lt : ∀ u ∈ rem, u < p := fun u hu => hus u (by rw [← hsp]; simp [hu])
    obtain ⟨nb, y, w', eb, hnb, hyf, hyrest, hyU, hyclr, hyoth, hy_hasR, hy_hasNext⟩ :=
      firstWitnessBody_eval hp2 hq us pref rem hsp w hw_lt hrem_lt x
        hflags.1 hflags.2 hxP hxQ hxW hxU hxclr hfnd
    have spb : Spec sIn sOut firstWitnessBody x y nb B :=
      Spec.of_eval_local eb (by
        have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
        dsimp only [L] at *
        omega)
    have hy_keep : ∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW → k ≠ sU → k.val < 15 →
        y.stacks k = a.stacks k := fun k h1 h2 h3 h4 hk15 =>
      (hyoth k h1 h2 h3 h4 hk15).trans (hxoth k h1 h2 h3 h4 hk15)
    have hyP : y.stacks sP = p.bits := (hy_keep sP (by decide) (by decide) (by decide) (by decide) (by decide)).trans hP
    have hyQ : y.stacks sQ = q.bits := (hy_keep sQ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hQ
    cases rem with
    | nil =>
        simp only [List.isEmpty_nil, Bool.not_true] at hyf
        rcases hyrest with ⟨h1s, h1b, h1W, h1_fnd, hfnd1⟩
        have hsp_nil : pref = us := by simpa using hsp
        refine ⟨nb, y, spb, pref, [], w, hsp, ?_, ?_, hw_lt, hyP, hyQ, h1W, hyU, hyclr,
          hy_keep, hy_hasR.trans hx_hasR, hy_hasNext.trans hx_hasNext⟩
        · simp [hyf, h1s, h1b]
        · simpa [hsp_nil] using hfnd1
    | cons u rest =>
        simp only [List.isEmpty_cons, Bool.not_false] at hyf
        rcases hyrest with ⟨hys, hyb, hyw, hyW, hyfnd⟩
        refine ⟨nb, y, spb, pref ++ [u], rest, w', by simpa [List.append_assoc] using hsp,
          by simp [hyf, hys, hyb], hyfnd, hyw, hyP, hyQ, hyW, hyU, hyclr,
          hy_keep, hy_hasR.trans hx_hasR, hy_hasNext.trans hx_hasNext⟩
  have hIa5 : I a₅ := ⟨[], us, 1, rfl, by simp [h5flag, h5Us, h5Bak], by simp [h5fnd],
    by omega, h5P, h5Q, ha5_W, h5U, h5clr,
    fun k _ _ hkw _ _ => ha5_keep k hkw, h5hasR, h5hasNext⟩
  have sp_loop : Spec sIn sOut (mkWhile rFlag firstWitnessBody) a₅ b_loop nl B :=
    Spec.while sIn sOut firstWitnessBody rFlag I B hinit hstep e_loop hIa5
  have hloop_bits : BitProgram.stackBits b_loop.stacks ≤ BitProgram.stackBits a.stacks + L := by
    have hlo_keep : ∀ k : Fin S, k ≠ sUs → k ≠ sUsBak → k ≠ sW → k ≠ sU → k.val < 15 →
        b_loop.stacks k = a.stacks k := fun k h1 h2 h3 h4 hk15 =>
      (hloth k h1 h2 h3 h4 hk15).trans (ha5_keep k h3)
    have hfw_lt : firstWitness p q us < p := by
      unfold firstWitness
      cases hf : (us.find? (fun u => decide (powMod p u q ≠ 1))) with
      | none => simpa using (by omega : 1 < p)
      | some u =>
          have hu_mem := List.mem_of_find?_eq_some hf
          exact hus u hu_mem
    refine stackBits_le_add_of_fw a b_loop L ?_ ?_ hlU hU hlclr hclr hlo_keep
    · rw [hlUs, hlBak, hUs, hBak]; simp
    · rw [hlW, hW]; simp only [List.length_nil, zero_add]; exact lt_prime_bits_length_le hfw_lt
  obtain ⟨nr, b, sp_rev, hnr, hrBak, hrUs, hro, hrreg, _⟩ :=
    revMove_spec (inS := sIn) (outS := sOut) (B := B) (by decide : sUsBak ≠ sUs) b_loop
      (by
        have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
        dsimp only [L] at *
        omega)
  refine ⟨_, b, Spec.seq sp₁ (Spec.seq sp₂ (Spec.seq sp₃ (Spec.seq sp₄ (Spec.seq sp₅ (Spec.seq sp_loop sp_rev))))), ?_, ?_, hrBak, ?_, ?_, ?_, ?_,
    (hrreg.2.1.symm.trans (hl_hasR.trans h5hasR)),
    (hrreg.2.2.symm.trans (hl_hasNext.trans h5hasNext))⟩
  · rw [hlBak, List.length_reverse] at hnr
    dsimp only [L] at *
    omega
  · rw [hrUs, hlBak, hlUs]; simp
  · rw [hro sW (by decide) (by decide), hlW]
  · rw [hro sU (by decide) (by decide), hlU]
  · intro k hk1 hk2
    rw [hro k (fin_ne_of_lt_ge 15 (by decide) hk1).symm (fin_ne_of_lt_ge 15 (by decide) hk1).symm]
    exact hlclr k hk1 hk2
  · intro k hku hkb hkw hkU hk15
    rw [hro k hkb hku, hloth k hku hkb hkw hkU hk15]
    exact ha5_keep k hkw

/-- 20. Sorted-run grouping + dividend/exponent computation `scanBodyPre`. -/
def dupBody : SCmd :=
  mkSeqList [
    mulToCore sRp sR sTmp3,
    moveStack sTmp3 sRp sTmp1,
    popNatFrame sFs sRNext sTmp1 rHasNext,
    mkIte rHasNext
      (mkSeqList [eqStack sR sRNext sTmp1 sTmp2, mkAtom (.copy rLoop rEq)])
      (mkAtom (.set rLoop false))
  ]

def scanBodyPre : SCmd :=
  mkSeqList [
    copyStack sR sRp sTmp1,
    popNatFrame sFs sRNext sTmp1 rHasNext,
    mkIte rHasNext
      (mkSeqList [eqStack sR sRNext sTmp1 sTmp2, mkAtom (.copy rLoop rEq)])
      (mkAtom (.set rLoop false)),
    mkWhile rLoop dupBody,
    divModCore sN sR,
    moveStack sDivQ sQ sTmp1,
    clearStack sDivR,
    divModCore sN sRp,
    moveStack sDivQ sE2 sTmp1,
    clearStack sDivR,
    clearStack sR,
    clearStack sRp,
    moveStack sRNext sR sTmp1,
    mkAtom (.copy rHasR rHasNext)
  ]

theorem dupLoop_eval {p r : ℕ} (hp2 : 2 ≤ p) (hr2 : 2 ≤ r) (hrp : r < p)
    (xs : List ℕ) (k : ℕ) (hk1 : 1 ≤ k)
    (hx_sort : xs.Pairwise (· ≤ ·))
    (hx_lt : ∀ z ∈ xs, z < p)
    (hx_pow : r ^ (k + 1 + (xs.takeWhile (· == r)).length) < p)
    (x0 : SState)
    (hLoop : x0.regs rLoop = true)
    (hR : x0.stacks sR = r.bits)
    (hRp : x0.stacks sRp = (r ^ k).bits)
    (hFs : x0.stacks sFs = encodeNatListBin xs)
    (hRN : x0.stacks sRNext = r.bits)
    (hclr : RangeCleared 15 27 x0.stacks) :
    let L := bitLen p + 1
    let tail := xs.dropWhile (· == r)
    ∃ n b, StructuredCalls.Eval (mkWhile rLoop dupBody) n x0 b ∧
      n ≤ ((xs.takeWhile (· == r)).length + 1) * (650 * L ^ 2 + 250) + 1 ∧
      b.stacks sRp = (r ^ (k + 1 + (xs.takeWhile (· == r)).length)).bits ∧
      TailNextMatch b.stacks tail ∧
      b.regs rHasNext = !tail.isEmpty ∧
      (match tail with | [] => True | z :: _ => z < p) ∧
      RangeCleared 15 27 b.stacks ∧
      (∀ s : Fin S, s ≠ sFs → s ≠ sRp → s ≠ sRNext → s.val < 15 → b.stacks s = x0.stacks s) := by
  let L := bitLen p + 1
  have hL : 2 ≤ L := by
    have : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  have hr_len : r.bits.length ≤ L := lt_prime_bits_length_le hrp
  induction xs generalizing k x0 with
  | nil =>
      have hk1_lt : r ^ (k + 1) < p := by simpa using hx_pow
      have hpow_k_lt : r ^ k < p := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)) hk1_lt
      have hRp_len : (r ^ k).bits.length ≤ L := lt_prime_bits_length_le hpow_k_lt
      have hmul_lt : (r ^ (k + 1)).bits.length ≤ L := lt_prime_bits_length_le hk1_lt
      have h18_26 : RangeCleared 18 26 x0.stacks := rangeCleared_mono hclr (by decide) (by decide)
      obtain ⟨n₁, b₁, e₁, hn₁, h1t3, h1clr18, h1lt18, _, _⟩ :=
        mulToCore_eval (by decide : sRp.val < 18) (by decide : sR.val < 18) (Or.inr rfl) x0 h18_26
      have h1t3' : b₁.stacks sTmp3 = (r ^ (k + 1)).bits := by
        rw [h1t3, hRp, hR, toNat_bits, toNat_bits, ← pow_succ]
      have h1t1 : b₁.stacks sTmp1 = [] := h1clr18 sTmp1 (by decide) (by decide)
      obtain ⟨n₂, b₂, e₂, hn₂, h2t3, h2Rp, h2t1, h2o, _⟩ :=
        moveStack_eval (by decide : sTmp3 ≠ sRp) (by decide : sTmp3 ≠ sTmp1) (by decide : sRp ≠ sTmp1) b₁ h1t1
      have h2Fs : b₂.stacks sFs = encodeNatListBin [] := by
        rw [h2o sFs (by decide) (by decide) (by decide), h1lt18 sFs (by decide) (by decide)]; exact hFs
      obtain ⟨n₃, b₃, e₃, hn₃, h3Fs, h3RN, h3t1, h3o, h3hn, _, _, _⟩ :=
        popNatFrame_eval (by decide : sFs ≠ sRNext) (by decide : sFs ≠ sTmp1) (by decide : sRNext ≠ sTmp1)
          rHasNext (by decide) (Or.inr (Or.inl rfl)) [] b₂ h2Fs h2t1
      simp only [List.isEmpty_nil, Bool.not_true] at h3hn
      simp only at h3Fs h3RN hn₃
      let b₄ : SState := ⟨Function.update b₃.regs rLoop false, b₃.stacks⟩
      have e₄ := eval_set b₃ rLoop false
      have h4clr : RangeCleared 15 27 b₄.stacks := by
        intro s hs1 hs2
        dsimp only [b₄]
        by_cases hst1 : s = sTmp1
        · subst hst1; exact h3t1
        · rw [h3o s (fin_ne_of_lt_ge 15 (by decide) hs1).symm (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1]
          by_cases hst3 : s = sTmp3
          · subst hst3; exact h2t3
          · rw [h2o s hst3 (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1]
            by_cases hs18 : 18 ≤ s.val
            · exact h1clr18 s hs18 (by have : s.val ≤ 27 := hs2; have : s.val ≠ 27 := fun hh => hst3 (Fin.ext hh); omega)
            · rw [h1lt18 s (by omega) hst3]; exact hclr s hs1 hs2
      refine ⟨_, b₄, .while_true hLoop (.seq e₁ (.seq e₂ (.seq e₃ (.ite_false h3hn e₄))))
          (.while_false (by simp [b₄])),
        ?_, ?_, ?_, ?_, ?_, h4clr, ?_⟩
      · have hb1Rp : (b₁.stacks sRp).length ≤ L := by rw [h1lt18 sRp (by decide) (by decide), hRp]; exact hRp_len
        have hb1t3 : (b₁.stacks sTmp3).length ≤ L := by rw [h1t3']; exact hmul_lt
        have hb2RN : (b₂.stacks sRNext).length ≤ L := by
          rw [h2o sRNext (by decide) (by decide) (by decide), h1lt18 sRNext (by decide) (by decide), hRN]
          exact hr_len
        have hb1s : (x0.stacks sTmp3).length = 0 := by rw [hclr sTmp3 (by decide) (by decide)]; rfl
        rw [hRp, hR, hb1s] at hn₁
        have hn1' := hn₁.trans (mulTo_step_bound hRp_len hr_len (Nat.zero_le L) hL)
        have h2L : 2 * L ≤ L ^ 2 := nat_two_mul_le_sq hL
        simp only [List.takeWhile_nil, List.length_nil, zero_add, Nat.one_mul]
        dsimp only [L] at *
        omega
      · dsimp only [b₄]; rw [h3o sRp (by decide) (by decide) (by decide), h2Rp, h1t3']; simp
      · dsimp only [b₄]; simp only [List.dropWhile_nil]; exact ⟨h3RN, h3Fs⟩
      · dsimp only [b₄]; rw [Function.update_of_ne (by decide : rHasNext ≠ rLoop)]; simp [h3hn]
      · simp
      · intro s hs1 hs2 hs3 hs15
        dsimp only [b₄]
        rw [h3o s hs1 hs3 (fin_ne_of_lt_ge 15 hs15 (by decide)),
          h2o s (fin_ne_of_lt_ge 15 hs15 (by decide)) hs2 (fin_ne_of_lt_ge 15 hs15 (by decide)),
          h1lt18 s (by omega) (fin_ne_of_lt_ge 15 hs15 (by decide))]
  | cons y ys ih =>
      have hy_lt : y < p := hx_lt y (by simp)
      have hy_len : y.bits.length ≤ L := lt_prime_bits_length_le hy_lt
      have hcw_y : (countWord y).length ≤ L := (countWord_length_le y).trans (max_le (by omega) hy_len)
      have hk1_lt : r ^ (k + 1) < p := by
        refine lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) ?_) hx_pow
        omega
      have hpow_k_lt : r ^ k < p := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)) hk1_lt
      have hRp_len : (r ^ k).bits.length ≤ L := lt_prime_bits_length_le hpow_k_lt
      have hmul_lt : (r ^ (k + 1)).bits.length ≤ L := lt_prime_bits_length_le hk1_lt
      have h18_26 : RangeCleared 18 26 x0.stacks := rangeCleared_mono hclr (by decide) (by decide)
      obtain ⟨n₁, b₁, e₁, hn₁, h1t3, h1clr18, h1lt18, _, _⟩ :=
        mulToCore_eval (by decide : sRp.val < 18) (by decide : sR.val < 18) (Or.inr rfl) x0 h18_26
      have h1t3' : b₁.stacks sTmp3 = (r ^ (k + 1)).bits := by
        rw [h1t3, hRp, hR, toNat_bits, toNat_bits, ← pow_succ]
      have h1t1 : b₁.stacks sTmp1 = [] := h1clr18 sTmp1 (by decide) (by decide)
      obtain ⟨n₂, b₂, e₂, hn₂, h2t3, h2Rp, h2t1, h2o, _⟩ :=
        moveStack_eval (by decide : sTmp3 ≠ sRp) (by decide : sTmp3 ≠ sTmp1) (by decide : sRp ≠ sTmp1) b₁ h1t1
      have h2Fs : b₂.stacks sFs = encodeNatListBin (y :: ys) := by
        rw [h2o sFs (by decide) (by decide) (by decide), h1lt18 sFs (by decide) (by decide)]; exact hFs
      obtain ⟨n₃, b₃, e₃, hn₃, h3Fs, h3RN, h3t1, h3o, h3hn, _, _, _⟩ :=
        popNatFrame_eval (by decide : sFs ≠ sRNext) (by decide : sFs ≠ sTmp1) (by decide : sRNext ≠ sTmp1)
          rHasNext (by decide) (Or.inr (Or.inl rfl)) (y :: ys) b₂ h2Fs h2t1
      simp only [List.isEmpty_cons, Bool.not_false] at h3hn
      simp only at h3Fs h3RN hn₃
      have h3clr : RangeCleared 15 27 b₃.stacks := by
        intro s hs1 hs2
        by_cases hst1 : s = sTmp1
        · subst hst1; exact h3t1
        · rw [h3o s (fin_ne_of_lt_ge 15 (by decide) hs1).symm (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1]
          by_cases hst3 : s = sTmp3
          · subst hst3; exact h2t3
          · rw [h2o s hst3 (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1]
            by_cases hs18 : 18 ≤ s.val
            · exact h1clr18 s hs18 (by have : s.val ≤ 27 := hs2; have : s.val ≠ 27 := fun hh => hst3 (Fin.ext hh); omega)
            · rw [h1lt18 s (by omega) hst3]; exact hclr s hs1 hs2
      have h3keep15 : ∀ s : Fin S, s ≠ sFs → s ≠ sRp → s ≠ sRNext → s.val < 15 →
          b₃.stacks s = x0.stacks s := fun s hs1 hs2 hs3 hs15 => by
        rw [h3o s hs1 hs3 (fin_ne_of_lt_ge 15 hs15 (by decide)),
          h2o s (fin_ne_of_lt_ge 15 hs15 (by decide)) hs2 (fin_ne_of_lt_ge 15 hs15 (by decide)),
          h1lt18 s (by omega) (fin_ne_of_lt_ge 15 hs15 (by decide))]
      have h3R : b₃.stacks sR = r.bits := (h3keep15 sR (by decide) (by decide) (by decide) (by decide)).trans hR
      obtain ⟨n₄, b₄, e₄, hn₄, h4stk, h4eq, h4reg⟩ :=
        eqStack_eval (by decide : sR ≠ sRNext) (by decide : sR ≠ sTmp1) (by decide : sR ≠ sTmp2)
          (by decide : sRNext ≠ sTmp1) (by decide : sRNext ≠ sTmp2) (by decide : sTmp1 ≠ sTmp2)
          b₃ h3t1 (h3clr sTmp2 (by decide) (by decide))
      let b₅ : SState := ⟨Function.update b₄.regs rLoop (b₄.regs rEq), b₄.stacks⟩
      have e₅ := eval_copy b₄ rLoop rEq
      have h5eq : b₅.regs rLoop = decide (r = y) := by
        dsimp only [b₅]; rw [Function.update_self, h4eq, h3R, h3RN, decide_eq_decide]
        constructor
        · intro h
          have ht := congrArg BinaryArithmetic.toNat h
          rw [toNat_bits, toNat_bits] at ht; exact ht
        · rintro rfl; rfl
      have h5hasNext : b₅.regs rHasNext = true := by
        dsimp only [b₅]; rw [Function.update_of_ne (by decide : rHasNext ≠ rLoop)]
        exact h4reg.2.2.symm.trans h3hn
      have h5_stack_eq : b₅.stacks = b₃.stacks := by dsimp only [b₅]; exact h4stk
      have h5_len : (b₄.stacks sR).length ≤ L ∧ (b₄.stacks sRNext).length ≤ L := by
        rw [h4stk, h3R, h3RN]; exact ⟨hr_len, hy_len⟩
      have h5s_bd :
          n₁ + (n₂ + (n₃ + (n₄ + 1 + 1))) + 1 ≤ 650 * L ^ 2 + 250 := by
        have hb1Rp : (b₁.stacks sRp).length ≤ L := by rw [h1lt18 sRp (by decide) (by decide), hRp]; exact hRp_len
        have hb1t3 : (b₁.stacks sTmp3).length ≤ L := by rw [h1t3']; exact hmul_lt
        have hb2RN : (b₂.stacks sRNext).length ≤ L := by
          rw [h2o sRNext (by decide) (by decide) (by decide), h1lt18 sRNext (by decide) (by decide), hRN]
          exact hr_len
        have hb1s : (x0.stacks sTmp3).length = 0 := by rw [hclr sTmp3 (by decide) (by decide)]; rfl
        rw [hRp, hR, hb1s] at hn₁
        rw [h3R, h3RN] at hn₄
        have hn1' := hn₁.trans (mulTo_step_bound hRp_len hr_len (Nat.zero_le L) hL)
        have h2L : 2 * L ≤ L ^ 2 := nat_two_mul_le_sq hL
        dsimp only [L] at *
        omega
      by_cases hyr : y = r
      · have ht5 : b₅.regs rLoop = true := by rw [h5eq, hyr]; simp
        have htw : ((y :: ys).takeWhile (· == r)) = r :: ys.takeWhile (· == r) := by
          rw [hyr]; simp [List.takeWhile_cons]
        have hdw : ((y :: ys).dropWhile (· == r)) = ys.dropWhile (· == r) := by
          rw [hyr]; simp [List.dropWhile_cons]
        have h5_lt : ∀ z ∈ ys, z < p := fun z hz => hx_lt z (by simp [hz])
        have h5_pow : r ^ (k + 1 + 1 + (ys.takeWhile (· == r)).length) < p := by
          rw [htw, List.length_cons] at hx_pow
          have : k + 1 + 1 + (ys.takeWhile (· == r)).length = k + 1 + ((ys.takeWhile (· == r)).length + 1) := by omega
          rw [this]; exact hx_pow
        have h5_Rp : b₅.stacks sRp = (r ^ (k + 1)).bits := by
          rw [h5_stack_eq, h3o sRp (by decide) (by decide) (by decide), h2Rp, h1t3']
        have h5_Fs : b₅.stacks sFs = encodeNatListBin ys := by
          rw [h5_stack_eq]; exact h3Fs
        have h5_RN : b₅.stacks sRNext = r.bits := by
          rw [h5_stack_eq, h3RN, hyr]
        have h5_R : b₅.stacks sR = r.bits := by rw [h5_stack_eq]; exact h3R
        obtain ⟨nt, fin, et, hnt, hRp_f, hTN_f, hhn_f, hz_f, hclr_f, hkeep_f⟩ :=
          ih (k + 1) (by omega) (List.pairwise_cons.mp hx_sort).2 h5_lt h5_pow
            b₅ ht5 h5_R h5_Rp h5_Fs h5_RN (by rw [h5_stack_eq]; exact h3clr)
        refine ⟨_, fin, .while_true hLoop (.seq e₁ (.seq e₂ (.seq e₃ (.ite_true h3hn (.seq e₄ e₅))))) et,
          ?_, ?_, ?_, ?_, ?_, hclr_f, ?_⟩
        · rw [htw, List.length_cons]
          have hmul_id : ((ys.takeWhile (· == r)).length + 1 + 1) * (650 * L ^ 2 + 250) =
              ((ys.takeWhile (· == r)).length + 1) * (650 * L ^ 2 + 250) + (650 * L ^ 2 + 250) := by ring
          dsimp only [L] at *
          omega
        · rw [hRp_f, htw, List.length_cons]; congr 2; omega
        · rw [hdw]; exact hTN_f
        · rw [hdw]; exact hhn_f
        · rw [hdw]; exact hz_f
        · intro s hs1 hs2 hs3 hs15
          rw [hkeep_f s hs1 hs2 hs3 hs15, h5_stack_eq]
          exact h3keep15 s hs1 hs2 hs3 hs15
      · have hf5 : b₅.regs rLoop = false := by
          rw [h5eq]; simp [Ne.symm hyr]
        have htw : ((y :: ys).takeWhile (· == r)) = [] := by
          simp [List.takeWhile_cons, beq_false_of_ne hyr]
        have hdw : ((y :: ys).dropWhile (· == r)) = y :: ys := by
          simp [List.dropWhile_cons, beq_false_of_ne hyr]
        refine ⟨_, b₅, .while_true hLoop (.seq e₁ (.seq e₂ (.seq e₃ (.ite_true h3hn (.seq e₄ e₅)))))
            (.while_false hf5),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [htw, List.length_nil]; dsimp only [L] at *; omega
        · rw [htw, List.length_nil, add_zero, h5_stack_eq, h3o sRp (by decide) (by decide) (by decide), h2Rp, h1t3']
        · rw [hdw]; exact ⟨by rw [h5_stack_eq]; exact h3RN, by rw [h5_stack_eq]; exact h3Fs⟩
        · rw [hdw]; simp [h5hasNext]
        · rw [hdw]; exact hy_lt
        · rw [h5_stack_eq]; exact h3clr
        · intro s hs1 hs2 hs3 hs15
          rw [h5_stack_eq]; exact h3keep15 s hs1 hs2 hs3 hs15

theorem scanBodyPre_eval {p r : ℕ} (hp2 : 2 ≤ p) (rest : List ℕ)
    (hr2 : 2 ≤ r) (hrp : r < p) (hsort : (r :: rest).Pairwise (· ≤ ·))
    (hmem : ∀ y ∈ r :: rest, 2 ≤ y ∧ y < p ∧ y ^ ((r :: rest).count y) < p)
    (a : SState)
    (hR : a.stacks sR = r.bits) (hFs : a.stacks sFs = encodeNatListBin rest)
    (hN : a.stacks sN = (p - 1).bits)
    (hRN : a.stacks sRNext = []) (hRp : a.stacks sRp = [])
    (hQ : a.stacks sQ = []) (hE2 : a.stacks sE2 = [])
    (hclr : RangeCleared 15 27 a.stacks) :
    let L := bitLen p + 1
    let dups := rest.takeWhile (· == r)
    let tail := rest.dropWhile (· == r)
    ∃ n b, StructuredCalls.Eval scanBodyPre n a b ∧
      n ≤ 2500 * L ^ 3 + 1000 ∧
      b.stacks sQ = ((p - 1) / r).bits ∧
      b.stacks sE2 = ((p - 1) / (r ^ (dups.length + 1))).bits ∧
      b.regs rHasR = !tail.isEmpty ∧
      FactorsHeadMatch b.stacks tail ∧
      b.stacks sRNext = [] ∧ b.stacks sRp = [] ∧
      RangeCleared 15 27 b.stacks ∧
      (∀ s : Fin S, s ≠ sR → s ≠ sFs → s ≠ sRNext → s ≠ sRp → s ≠ sQ → s ≠ sE2 → s.val < 15 →
        b.stacks s = a.stacks s) := by
  let L := bitLen p + 1
  have hL : 2 ≤ L := by
    have : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  have hr_len : r.bits.length ≤ L := lt_prime_bits_length_le hrp
  have hN_len : (p - 1).bits.length ≤ L := lt_prime_bits_length_le (by omega)
  have hprops := sorted_span_props hsort
  rcases hprops with ⟨_, _, htailSort, _, hcount_r, _, _⟩
  have hpow_lt : r ^ ((rest.takeWhile (· == r)).length + 1) < p := by
    rw [← hcount_r]; exact (hmem r (by simp)).2.2
  have hdups_bd : (rest.takeWhile (· == r)).length + 1 ≤ L := by
    have h2p : 2 ^ ((rest.takeWhile (· == r)).length + 1) ≤ r ^ ((rest.takeWhile (· == r)).length + 1) :=
      Nat.pow_le_pow_left hr2 _
    have hclog : p ≤ 2 ^ bitLen p := (Nat.clog_le_iff_le_pow (by decide)).mp le_rfl
    have hlt2 : 2 ^ ((rest.takeWhile (· == r)).length + 1) < 2 ^ L := by
      calc 2 ^ ((rest.takeWhile (· == r)).length + 1)
          ≤ r ^ ((rest.takeWhile (· == r)).length + 1) := h2p
        _ < p := hpow_lt
        _ ≤ 2 ^ bitLen p := hclog
        _ < 2 ^ L := by rw [pow_succ']; have := pow_pos (by decide : 0 < 2) (bitLen p); omega
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt2)
  have ht1 : a.stacks sTmp1 = [] := hclr sTmp1 (by decide) (by decide)
  obtain ⟨n₁, b₁, e₁, hn₁, h1R, h1Rp, h1t1, h1o, _⟩ :=
    copyStack_eval (by decide : sR ≠ sRp) (by decide : sR ≠ sTmp1) (by decide : sRp ≠ sTmp1) a ht1
  have h1Fs : b₁.stacks sFs = encodeNatListBin rest := (h1o sFs (by decide) (by decide)).trans hFs
  have h1RN : b₁.stacks sRNext = [] := (h1o sRNext (by decide) (by decide)).trans hRN
  obtain ⟨n₂, b₂, e₂, hn₂, h2Fs, h2RN, h2t1, h2o, h2hn, _, _, _⟩ :=
    popNatFrame_eval (by decide : sFs ≠ sRNext) (by decide : sFs ≠ sTmp1) (by decide : sRNext ≠ sTmp1)
      rHasNext (by decide) (Or.inr (Or.inl rfl)) rest b₁ h1Fs h1t1
  have h2clr : RangeCleared 15 27 b₂.stacks := by
    intro s hs1 hs2
    by_cases hst1 : s = sTmp1
    · subst hst1; exact h2t1
    · rw [h2o s (fin_ne_of_lt_ge 15 (by decide) hs1).symm (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1]
      by_cases hst1' : s = sTmp1
      · exact absurd hst1' hst1
      · rw [h1o s (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1']; exact hclr s hs1 hs2
  have h2keep15 : ∀ s : Fin S, s ≠ sFs → s ≠ sRp → s ≠ sRNext → s.val < 15 → b₂.stacks s = a.stacks s :=
    fun s hs1 hs2 hs3 hs15 => by
      rw [h2o s hs1 hs3 (fin_ne_of_lt_ge 15 hs15 (by decide)),
        h1o s hs2 (fin_ne_of_lt_ge 15 hs15 (by decide))]
  have h2R : b₂.stacks sR = r.bits := (h2keep15 sR (by decide) (by decide) (by decide) (by decide)).trans hR
  have h2Rp : b₂.stacks sRp = (r ^ 1).bits := by
    rw [h2o sRp (by decide) (by decide) (by decide), h1Rp, hR]; simp
  -- Step 3-4: ite rHasNext + mkWhile rLoop dupBody
  have hpre_loop :
      ∃ ni nw mid bl,
        StructuredCalls.Eval
          (mkIte rHasNext (mkSeqList [eqStack sR sRNext sTmp1 sTmp2, mkAtom (.copy rLoop rEq)]) (mkAtom (.set rLoop false)))
          ni b₂ mid ∧
        StructuredCalls.Eval (mkWhile rLoop dupBody) nw mid bl ∧
        ni + nw ≤ (52 * L + 14) + ((rest.takeWhile (· == r)).length + 1) * (650 * L ^ 2 + 250) + 1 ∧
        bl.stacks sRp = (r ^ ((rest.takeWhile (· == r)).length + 1)).bits ∧
        TailNextMatch bl.stacks (rest.dropWhile (· == r)) ∧
        bl.regs rHasNext = !(rest.dropWhile (· == r)).isEmpty ∧
        (match rest.dropWhile (· == r) with | [] => True | z :: _ => z < p) ∧
        RangeCleared 15 27 bl.stacks ∧
        (∀ s : Fin S, s ≠ sFs → s ≠ sRp → s ≠ sRNext → s.val < 15 → bl.stacks s = a.stacks s) := by
    cases rest with
    | nil =>
        simp only [List.isEmpty_nil, Bool.not_true] at h2hn h2Fs h2RN
        let b₃ : SState := ⟨Function.update b₂.regs rLoop false, b₂.stacks⟩
        have e₃ := eval_set b₂ rLoop false
        refine ⟨_, _, b₃, b₃, .ite_false h2hn e₃, .while_false (by simp [b₃]),
          by simp only [List.takeWhile_nil, List.length_nil, zero_add, Nat.one_mul]; linarith only [hL, Nat.zero_le (650 * L ^ 2)],
          by simp [b₃, h2Rp],
          by simp only [List.dropWhile_nil]; exact ⟨h2RN, h2Fs⟩,
          by simp only [List.dropWhile_nil, List.isEmpty_nil, Bool.not_true]; dsimp only [b₃]; rw [Function.update_of_ne (by decide : rHasNext ≠ rLoop)]; exact h2hn,
          by simp, h2clr, fun s hs1 hs2 hs3 hs15 => h2keep15 s hs1 hs2 hs3 hs15⟩
    | cons y ys =>
        simp only [List.isEmpty_cons, Bool.not_false] at h2hn h2Fs h2RN
        have hy_lt : y < p := (hmem y (by simp)).2.1
        have hy_len : y.bits.length ≤ L := lt_prime_bits_length_le hy_lt
        obtain ⟨n₃, b₃, e₃, hn₃, h3stk, h3eq, h3reg⟩ :=
          eqStack_eval (by decide : sR ≠ sRNext) (by decide : sR ≠ sTmp1) (by decide : sR ≠ sTmp2)
            (by decide : sRNext ≠ sTmp1) (by decide : sRNext ≠ sTmp2) (by decide : sTmp1 ≠ sTmp2)
            b₂ h2t1 (h2clr sTmp2 (by decide) (by decide))
        let b₄ : SState := ⟨Function.update b₃.regs rLoop (b₃.regs rEq), b₃.stacks⟩
        have e₄ := eval_copy b₃ rLoop rEq
        have h4eq : b₄.regs rLoop = decide (r = y) := by
          dsimp only [b₄]; rw [Function.update_self, h3eq, h2R, h2RN, decide_eq_decide]
          constructor
          · intro h; have ht := congrArg BinaryArithmetic.toNat h; rw [toNat_bits, toNat_bits] at ht; exact ht
          · rintro rfl; rfl
        have h4hn : b₄.regs rHasNext = true := by
          dsimp only [b₄]; rw [Function.update_of_ne (by decide : rHasNext ≠ rLoop), ← h3reg.2.2, h2hn]
        have h4_bd : n₃ + 1 + 1 ≤ 52 * L + 14 := by rw [h2R, h2RN] at hn₃; linarith only [hn₃, hr_len, hy_len]
        by_cases hyr : y = r
        · have ht4 : b₄.regs rLoop = true := by rw [h4eq, hyr]; simp
          have htw : ((y :: ys).takeWhile (· == r)) = r :: ys.takeWhile (· == r) := by rw [hyr]; simp [List.takeWhile_cons]
          have hdw : ((y :: ys).dropWhile (· == r)) = ys.dropWhile (· == r) := by rw [hyr]; simp [List.dropWhile_cons]
          have hys_sort : ys.Pairwise (· ≤ ·) :=
            (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2
          have hys_lt : ∀ z ∈ ys, z < p := fun z hz => (hmem z (by simp [hz])).2.1
          have hys_pow : r ^ (1 + 1 + (ys.takeWhile (· == r)).length) < p := by
            rw [htw, List.length_cons] at hpow_lt
            have : 1 + 1 + (ys.takeWhile (· == r)).length = (ys.takeWhile (· == r)).length + 1 + 1 := by omega
            rw [this]; exact hpow_lt
          obtain ⟨nd, fin, ed, hnd, hdRp, hdTN, hdhn, hdz, hdclr, hdk⟩ :=
            dupLoop_eval hp2 hr2 hrp ys 1 le_rfl hys_sort hys_lt hys_pow b₄ ht4
              (by dsimp only [b₄]; rw [h3stk]; exact h2R)
              (by dsimp only [b₄]; rw [h3stk]; exact h2Rp)
              (by dsimp only [b₄]; rw [h3stk]; exact h2Fs)
              (by dsimp only [b₄]; rw [h3stk, h2RN, hyr])
              (by dsimp only [b₄]; rw [h3stk]; exact h2clr)
          refine ⟨_, _, b₄, fin, .ite_true h2hn (.seq e₃ e₄), ed, ?_, ?_, ?_, ?_, ?_, hdclr, ?_⟩
          · rw [htw, List.length_cons]
            have hmul : ((ys.takeWhile (· == r)).length + 1 + 1) * (650 * L ^ 2 + 250) =
                ((ys.takeWhile (· == r)).length + 1) * (650 * L ^ 2 + 250) + (650 * L ^ 2 + 250) := by ring
            dsimp only [L] at *
            omega
          · rw [hdRp, htw, List.length_cons]; congr 2; omega
          · rw [hdw]; exact hdTN
          · rw [hdw]; exact hdhn
          · rw [hdw]; exact hdz
          · intro s hs1 hs2 hs3 hs15
            rw [hdk s hs1 hs2 hs3 hs15]; dsimp only [b₄]; rw [h3stk]
            exact h2keep15 s hs1 hs2 hs3 hs15
        · have hf4 : b₄.regs rLoop = false := by rw [h4eq]; simp [Ne.symm hyr]
          have htw : ((y :: ys).takeWhile (· == r)) = [] := by simp [List.takeWhile_cons, beq_false_of_ne hyr]
          have hdw : ((y :: ys).dropWhile (· == r)) = y :: ys := by simp [List.dropWhile_cons, beq_false_of_ne hyr]
          refine ⟨_, _, b₄, b₄, .ite_true h2hn (.seq e₃ e₄), .while_false hf4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [htw, List.length_nil]; dsimp only [L] at *; omega
          · dsimp only [b₄]; rw [h3stk, h2Rp, htw, List.length_nil]
          · rw [hdw]; exact ⟨by dsimp only [b₄]; rw [h3stk, h2RN], by dsimp only [b₄]; rw [h3stk, h2Fs]⟩
          · rw [hdw]; simp [h4hn]
          · rw [hdw]; exact hy_lt
          · dsimp only [b₄]; rw [h3stk]; exact h2clr
          · intro s hs1 hs2 hs3 hs15
            dsimp only [b₄]; rw [h3stk]; exact h2keep15 s hs1 hs2 hs3 hs15
  obtain ⟨ni, nw, mid, bl, e_ite, e_whl, hnl, hlRp, hlTN, hlhn, hlz, hlclr, hlkeep⟩ := hpre_loop
  -- Post-dup division steps
  let rp := r ^ ((rest.takeWhile (· == r)).length + 1)
  have hrp_pos : 0 < rp := Nat.pow_pos (by omega : 0 < r)
  have hrp_len : rp.bits.length ≤ L := lt_prime_bits_length_le hpow_lt
  have hlN : bl.stacks sN = (p - 1).bits :=
    (hlkeep sN (by decide) (by decide) (by decide) (by decide)).trans hN
  have hlR : bl.stacks sR = r.bits :=
    (hlkeep sR (by decide) (by decide) (by decide) (by decide)).trans hR
  have hlQ : bl.stacks sQ = [] :=
    (hlkeep sQ (by decide) (by decide) (by decide) (by decide)).trans hQ
  have hlE2 : bl.stacks sE2 = [] :=
    (hlkeep sE2 (by decide) (by decide) (by decide) (by decide)).trans hE2
  obtain ⟨nd1, d₁, ed1, hnd1, hd1Q, hd1R, hd1N, hd1D, hd1t1, hd1t2, hd1o, hreg_d1⟩ :=
    divModCore_eval (by decide : sN.val < 18 ∨ sN = sTmp3) (by decide : sR.val < 18)
      bl (by rw [hlR, toNat_bits]; omega) (rangeCleared_mono hlclr (by decide) (by decide))
  obtain ⟨nm1, m₁, em1, hnm1, hm1Q, hm1dQ, hm1t1, hm1o, hreg_m1⟩ :=
    moveStack_eval (by decide : sDivQ ≠ sQ) (by decide : sDivQ ≠ sTmp1) (by decide : sQ ≠ sTmp1) d₁ hd1t1
  obtain ⟨nc1, c₁, ec1, hnc1, hc1R, hc1o, hreg_c1⟩ := clearStack_eval sDivR m₁
  have h15_d1 : ∀ s : Fin S, 15 ≤ s.val → s.val ≤ 20 → d₁.stacks s = [] := fun s hs1 hs2 => by
    rw [hd1o s (Or.inl (by omega))]; exact hlclr s hs1 (by omega)
  have hc1_clr : RangeCleared 15 27 c₁.stacks := by
    intro s hs1 hs2
    by_cases hsR : s = sDivR
    · subst hsR; exact hc1R
    · rw [hc1o s hsR]
      by_cases hst1 : s = sTmp1
      · subst hst1; exact hm1t1
      · by_cases hsQ : s = sDivQ
        · subst hsQ; exact hm1Q
        · rw [hm1o s hsQ (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1]
          by_cases hst3 : s = sTmp3
          · subst hst3; rw [hd1o sTmp3 (Or.inr rfl)]; exact hlclr sTmp3 (by decide) (by decide)
          · by_cases hs21 : s.val < 21
            · exact h15_d1 s hs1 (by omega)
            · have : s.val = 21 ∨ s.val = 22 ∨ s.val = 26 := by
                have := Fin.isLt s
                have h23 : s.val ≠ 23 := fun hh => hsQ (Fin.ext hh)
                have h24 : s.val ≠ 24 := fun hh => hsR (Fin.ext hh)
                have h25 : s.val ≠ 25 := fun hh => hst1 (Fin.ext hh)
                have h27 : s.val ≠ 27 := fun hh => hst3 (Fin.ext hh)
                omega
              rcases this with hv | hv | hv
              · have : s = sDivN := Fin.ext hv; rw [this]; exact hd1N
              · have : s = sDivD := Fin.ext hv; rw [this]; exact hd1D
              · have : s = sTmp2 := Fin.ext hv; rw [this]; exact hd1t2
  have hc1_lt18 : ∀ s : Fin S, s ≠ sQ → s.val < 18 → c₁.stacks s = bl.stacks s := fun s hsq hs18 => by
    rw [hc1o s (fin_ne_of_lt_ge 18 hs18 (by decide)),
      hm1o s (fin_ne_of_lt_ge 18 hs18 (by decide)) hsq (fin_ne_of_lt_ge 18 hs18 (by decide)),
      hd1o s (Or.inl (by omega))]
  have hc1_Q : c₁.stacks sQ = ((p - 1) / r).bits := by
    rw [hc1o sQ (by decide), hm1dQ, hd1Q, hlN, hlR, toNat_bits, toNat_bits]
  -- Second divModCore sN sRp
  obtain ⟨nd2, d₂, ed2, hnd2, hd2Q, hd2R, hd2N, hd2D, hd2t1, hd2t2, hd2o, hreg_d2⟩ :=
    divModCore_eval (by decide : sN.val < 18 ∨ sN = sTmp3) (by decide : sRp.val < 18)
      c₁ (by rw [hc1_lt18 sRp (by decide) (by decide), hlRp, toNat_bits]; exact hrp_pos)
      (rangeCleared_mono hc1_clr (by decide) (by decide))
  obtain ⟨nm2, m₂, em2, hnm2, hm2Q, hm2dE2, hm2t1, hm2o, hreg_m2⟩ :=
    moveStack_eval (by decide : sDivQ ≠ sE2) (by decide : sDivQ ≠ sTmp1) (by decide : sE2 ≠ sTmp1) d₂ hd2t1
  obtain ⟨nc2, c₂, ec2, hnc2, hc2R, hc2o, hreg_c2⟩ := clearStack_eval sDivR m₂
  have hc2_clr : RangeCleared 15 27 c₂.stacks := by
    intro s hs1 hs2
    by_cases hsR : s = sDivR
    · subst hsR; exact hc2R
    · rw [hc2o s hsR]
      by_cases hst1 : s = sTmp1
      · subst hst1; exact hm2t1
      · by_cases hsQ : s = sDivQ
        · subst hsQ; exact hm2Q
        · rw [hm2o s hsQ (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1]
          by_cases hst3 : s = sTmp3
          · subst hst3; rw [hd2o sTmp3 (Or.inr rfl)]; exact hc1_clr sTmp3 (by decide) (by decide)
          · by_cases hs21 : s.val < 21
            · rw [hd2o s (Or.inl hs21)]; exact hc1_clr s hs1 hs2
            · have : s.val = 21 ∨ s.val = 22 ∨ s.val = 26 := by
                have := Fin.isLt s
                have h23 : s.val ≠ 23 := fun hh => hsQ (Fin.ext hh)
                have h24 : s.val ≠ 24 := fun hh => hsR (Fin.ext hh)
                have h25 : s.val ≠ 25 := fun hh => hst1 (Fin.ext hh)
                have h27 : s.val ≠ 27 := fun hh => hst3 (Fin.ext hh)
                omega
              rcases this with hv | hv | hv
              · have : s = sDivN := Fin.ext hv; rw [this]; exact hd2N
              · have : s = sDivD := Fin.ext hv; rw [this]; exact hd2D
              · have : s = sTmp2 := Fin.ext hv; rw [this]; exact hd2t2
  have hc2_lt18 : ∀ s : Fin S, s ≠ sE2 → s.val < 18 → c₂.stacks s = c₁.stacks s := fun s hse hs18 => by
    rw [hc2o s (fin_ne_of_lt_ge 18 hs18 (by decide)),
      hm2o s (fin_ne_of_lt_ge 18 hs18 (by decide)) hse (fin_ne_of_lt_ge 18 hs18 (by decide)),
      hd2o s (Or.inl (by omega))]
  have hc2_E2 : c₂.stacks sE2 = ((p - 1) / rp).bits := by
    rw [hc2o sE2 (by decide), hm2dE2, hd2Q,
      hc1_lt18 sN (by decide) (by decide), hlN,
      hc1_lt18 sRp (by decide) (by decide), hlRp, toNat_bits, toNat_bits]
  -- Cleanup sR, sRp, moveStack sRNext sR, copy rHasR rHasNext
  obtain ⟨nsR, k₁, ek1, hnsR, hk1R, hk1o, hreg_k1⟩ := clearStack_eval sR c₂
  obtain ⟨nsRp, k₂, ek2, hnsRp, hk2Rp, hk2o, hreg_k2⟩ := clearStack_eval sRp k₁
  obtain ⟨nmR, k₃, ek3, hnmR, hk3RN, hk3R, hk3t1, hk3o, hreg_k3⟩ :=
    moveStack_eval (by decide : sRNext ≠ sR) (by decide : sRNext ≠ sTmp1) (by decide : sR ≠ sTmp1)
      k₂ (by rw [hk2o sTmp1 (by decide), hk1o sTmp1 (by decide)]; exact hc2_clr sTmp1 (by decide) (by decide))
  let fin : SState := ⟨Function.update k₃.regs rHasR (k₃.regs rHasNext), k₃.stacks⟩
  have efin := eval_copy k₃ rHasR rHasNext
  -- Collect step bounds cleanly
  have hb1_lt18 : ∀ s : Fin S, s ≠ sRp → s.val < 15 → b₁.stacks s = a.stacks s := fun s hs hs15 =>
    h1o s hs (fin_ne_of_lt_ge 15 hs15 (by decide))
  have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
  have hd1Q_len : (d₁.stacks sDivQ).length ≤ L := by
    rw [hd1Q, hlN, hlR, toNat_bits, toNat_bits]; exact lt_prime_bits_length_le (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  have hd1R_len : (d₁.stacks sDivR).length ≤ L := by
    rw [hd1R, hlN, hlR, toNat_bits, toNat_bits]
    exact lt_prime_bits_length_le (lt_trans (Nat.mod_lt _ (by omega)) hrp)
  have hd2Q_len : (d₂.stacks sDivQ).length ≤ L := by
    rw [hd2Q, hc1_lt18 sN (by decide) (by decide), hlN, hc1_lt18 sRp (by decide) (by decide), hlRp, toNat_bits, toNat_bits]
    exact lt_prime_bits_length_le (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  have hd2R_len : (d₂.stacks sDivR).length ≤ L := by
    rw [hd2R, hc1_lt18 sN (by decide) (by decide), hlN, hc1_lt18 sRp (by decide) (by decide), hlRp, toNat_bits, toNat_bits]
    exact lt_prime_bits_length_le (lt_trans (Nat.mod_lt _ hrp_pos) hpow_lt)
  have h1s_len : (a.stacks sR).length ≤ L ∧ (a.stacks sRp).length ≤ L := by
    rw [hR, hRp]; exact ⟨hr_len, by simp⟩
  have hn1_bd : n₁ ≤ 9 * L + 6 := by
    rw [hR, hRp] at hn₁; simp only [List.length_nil] at hn₁; dsimp only [L] at *; omega
  have hn2_bd : n₂ ≤ 25 * L + 25 := by
    have h1RN0 : (b₁.stacks sRNext).length = 0 := by rw [h1RN]; rfl
    rw [h1RN0] at hn₂
    cases rest with
    | nil => simp at hn₂; dsimp only [L] at *; omega
    | cons y ys =>
        simp only at hn₂
        have hcw : (countWord y).length ≤ L :=
          (countWord_length_le y).trans (max_le (by omega) (lt_prime_bits_length_le (hmem y (by simp)).2.1))
        dsimp only [L] at *; omega
  have hnl_bd : ni + nw ≤ 650 * L ^ 3 + 310 * L + 15 := by
    have : ((rest.takeWhile (· == r)).length + 1) * (650 * L ^ 2 + 250) ≤ L * (650 * L ^ 2 + 250) :=
      Nat.mul_le_mul_right _ hdups_bd
    have hmul : L * (650 * L ^ 2 + 250) = 650 * L ^ 3 + 250 * L := by ring
    dsimp only [L] at *
    omega
  have hnd1_bd : nd1 ≤ 800 * L ^ 2 + 60 := by
    rw [hlN, hlR] at hnd1; exact hnd1.trans (divMod_step_bound hN_len hr_len hL)
  have hnm1_bd : nm1 ≤ 8 * L + 6 := by
    have h1q : (d₁.stacks sQ).length = 0 := by rw [hd1o sQ (Or.inl (by decide)), hlQ]; rfl
    rw [h1q] at hnm1; dsimp only [L] at *; omega
  have hnc1_bd : nc1 ≤ 3 * L + 2 := by rw [hm1o sDivR (by decide) (by decide) (by decide)] at hnc1; dsimp only [L] at *; omega
  have hnd2_bd : nd2 ≤ 800 * L ^ 2 + 60 := by
    rw [hc1_lt18 sN (by decide) (by decide), hlN, hc1_lt18 sRp (by decide) (by decide), hlRp] at hnd2
    exact hnd2.trans (divMod_step_bound hN_len hrp_len hL)
  have hnm2_bd : nm2 ≤ 8 * L + 6 := by
    have hd2E : (d₂.stacks sE2).length = 0 := by
      rw [hd2o sE2 (Or.inl (by decide)), hc1_lt18 sE2 (by decide) (by decide), hlE2]; rfl
    rw [hd2E] at hnm2; dsimp only [L] at *; omega
  have hnc2_bd : nc2 ≤ 3 * L + 2 := by rw [hm2o sDivR (by decide) (by decide) (by decide)] at hnc2; dsimp only [L] at *; omega
  have hnsR_bd : nsR ≤ 3 * L + 2 := by
    have : c₂.stacks sR = r.bits := by
      rw [hc2_lt18 sR (by decide) (by decide), hc1_lt18 sR (by decide) (by decide), hlR]
    rw [this] at hnsR; dsimp only [L] at *; omega
  have hnsRp_bd : nsRp ≤ 3 * L + 2 := by
    have : k₁.stacks sRp = rp.bits := by
      rw [hk1o sRp (by decide), hc2_lt18 sRp (by decide) (by decide), hc1_lt18 sRp (by decide) (by decide), hlRp]
    rw [this] at hnsRp; dsimp only [L] at *; omega
  have hnmR_bd : nmR ≤ 8 * L + 6 := by
    have hk2R : (k₂.stacks sR).length = 0 := by rw [hk2o sR (by decide), hk1R]; rfl
    have hk2RN : (k₂.stacks sRNext).length ≤ L := by
      rw [hk2o sRNext (by decide), hk1o sRNext (by decide),
        hc2_lt18 sRNext (by decide) (by decide), hc1_lt18 sRNext (by decide) (by decide)]
      cases htd : rest.dropWhile (· == r) with
      | nil => simp only [htd] at hlTN; simp [hlTN.1]
      | cons z _ =>
          simp only [htd] at hlTN hlz
          rw [hlTN.1]; exact lt_prime_bits_length_le hlz
    rw [hk2R] at hnmR; dsimp only [L] at *; omega
  have hL2_L3 : 1600 * L ^ 2 ≤ 800 * L ^ 3 := by
    have h2sq : 2 * L ^ 2 ≤ L ^ 3 := nat_two_mul_sq_le_cube hL
    omega
  have hfin_lt15 : ∀ s : Fin S, s ≠ sR → s ≠ sRp → s ≠ sRNext → s.val < 15 →
      fin.stacks s = c₂.stacks s := fun s hsR hsRp hsRN hs15 => by
    dsimp only [fin]
    rw [hk3o s hsRN hsR (fin_ne_of_lt_ge 15 hs15 (by decide)), hk2o s hsRp, hk1o s hsR]
  have hfin_clr : RangeCleared 15 27 fin.stacks := by
    intro s hs1 hs2
    dsimp only [fin]
    by_cases hst1 : s = sTmp1
    · subst hst1; exact hk3t1
    · rw [hk3o s (fin_ne_of_lt_ge 15 (by decide) hs1).symm (fin_ne_of_lt_ge 15 (by decide) hs1).symm hst1,
        hk2o s (fin_ne_of_lt_ge 15 (by decide) hs1).symm,
        hk1o s (fin_ne_of_lt_ge 15 (by decide) hs1).symm]
      exact hc2_clr s hs1 hs2
  have hfin_reg : k₃.regs rHasNext = bl.regs rHasNext := by
    have hr := regPreserved_trans hreg_d1 (regPreserved_trans hreg_m1 (regPreserved_trans hreg_c1
      (regPreserved_trans hreg_d2 (regPreserved_trans hreg_m2 (regPreserved_trans hreg_c2
        (regPreserved_trans hreg_k1 (regPreserved_trans hreg_k2 hreg_k3)))))))
    exact hr.2.2.symm
  refine ⟨_, fin,
    .seq e₁ (.seq e₂ (.seq e_ite (.seq e_whl (.seq ed1 (.seq em1 (.seq ec1 (.seq ed2 (.seq em2
      (.seq ec2 (.seq ek1 (.seq ek2 (.seq ek3 efin)))))))))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfin_clr, ?_⟩
  · dsimp only [L] at *; omega
  · rw [hfin_lt15 sQ (by decide) (by decide) (by decide) (by decide), hc2_lt18 sQ (by decide) (by decide), hc1_Q]
  · dsimp only [fin]; rw [hk3o sE2 (by decide) (by decide) (by decide), hk2o sE2 (by decide), hk1o sE2 (by decide), hc2_E2]
  · dsimp only [fin]; rw [Function.update_self, hfin_reg, hlhn]
  · cases htd : rest.dropWhile (· == r) with
    | nil =>
        simp only [htd] at hlTN
        constructor
        · dsimp only [fin]; rw [hk3R, hk2o sRNext (by decide), hk1o sRNext (by decide),
            hc2_lt18 sRNext (by decide) (by decide), hc1_lt18 sRNext (by decide) (by decide), hlTN.1]
        · rw [hfin_lt15 sFs (by decide) (by decide) (by decide) (by decide),
            hc2_lt18 sFs (by decide) (by decide), hc1_lt18 sFs (by decide) (by decide), hlTN.2]
    | cons z zs =>
        simp only [htd] at hlTN
        constructor
        · dsimp only [fin]; rw [hk3R, hk2o sRNext (by decide), hk1o sRNext (by decide),
            hc2_lt18 sRNext (by decide) (by decide), hc1_lt18 sRNext (by decide) (by decide), hlTN.1]
        · rw [hfin_lt15 sFs (by decide) (by decide) (by decide) (by decide),
            hc2_lt18 sFs (by decide) (by decide), hc1_lt18 sFs (by decide) (by decide), hlTN.2]
  · dsimp only [fin]; exact hk3RN
  · dsimp only [fin]; rw [hk3o sRp (by decide) (by decide) (by decide), hk2Rp]
  · intro s hsR hsFs hsRN hsRp hsQ hsE2 hs15
    rw [hfin_lt15 s hsR hsRp hsRN hs15, hc2_lt18 s hsE2 (by omega), hc1_lt18 s hsQ (by omega)]
    exact hlkeep s hsFs hsRp hsRN hs15

/-- 21. Modular-exponentiation accumulator update `scanBodyPost` and outer `scanBody` / `mainCmd`. -/
def scanBodyPost : SCmd :=
  mkSeqList [
    powModCmd sP sW sE2 sQ,
    clearStack sW,
    clearStack sE2,
    mulMod sAns sQ sP sAns,
    clearStack sQ
  ]

def scanBody : SCmd :=
  mkSeqList [scanBodyPre, firstWitnessCmd, scanBodyPost]

theorem scanBodyPost_eval {p acc w e2 : ℕ} (hp2 : 2 ≤ p)
    (hacc : acc < p) (hw : w < p) (he2 : e2 < p)
    (a : SState)
    (hP : a.stacks sP = p.bits) (hAns : a.stacks sAns = acc.bits)
    (hW : a.stacks sW = w.bits) (hE2 : a.stacks sE2 = e2.bits)
    (hQ : (a.stacks sQ).length ≤ bitLen p + 1)
    (hclr : RangeCleared 15 27 a.stacks) :
    let L := bitLen p + 1
    ∃ n b, StructuredCalls.Eval scanBodyPost n a b ∧
      n ≤ 140000 * L ^ 3 + 1000 ∧
      b.stacks sAns = ((acc * powMod p w e2) % p).bits ∧
      b.stacks sW = [] ∧ b.stacks sE2 = [] ∧ b.stacks sQ = [] ∧
      RangeCleared 15 27 b.stacks ∧
      (∀ k : Fin S, k ≠ sAns → k ≠ sW → k ≠ sE2 → k ≠ sQ → k.val < 15 →
        b.stacks k = a.stacks k) ∧
      RegPreserved a b := by
  let L := bitLen p + 1
  have hL : 2 ≤ L := by
    have : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  have hP_len : p.bits.length ≤ L := prime_bits_length_le hp2
  have hacc_len : acc.bits.length ≤ L := lt_prime_bits_length_le hacc
  have hw_len : w.bits.length ≤ L := lt_prime_bits_length_le hw
  have he2_len : e2.bits.length ≤ L := lt_prime_bits_length_le he2
  let v := powMod p w e2
  have hv_lt : v < p := by rw [show v = powMod p w e2 from rfl, powMod_eq]; exact Nat.mod_lt _ (by omega)
  have hv_len : v.bits.length ≤ L := lt_prime_bits_length_le hv_lt
  obtain ⟨n₁, b₁, e₁, hn₁, h1Q, h1ge15, h1lt15, h1reg⟩ :=
    powModCmd_eval (by decide : sP.val < 15) (by decide : sW.val < 15)
      (by decide : sE2.val < 15) (Or.inl (by decide : sQ.val < 15)) a
      (by rw [hP, toNat_bits]; exact hp2) hclr
  have h1Q' : b₁.stacks sQ = v.bits := by
    rw [h1Q, hP, hW, hE2, toNat_bits, toNat_bits, toNat_bits]
  obtain ⟨n₂, b₂, e₂, hn₂, h2W, h2o, h2reg⟩ := clearStack_eval sW b₁
  obtain ⟨n₃, b₃, e₃, hn₃, h3E2, h3o, h3reg⟩ := clearStack_eval sE2 b₂
  have h3clr18 : RangeCleared 18 27 b₃.stacks := fun k hk1 _ => by
    rw [h3o k (fin_ne_of_lt_ge 15 (by decide) (by omega)).symm,
      h2o k (fin_ne_of_lt_ge 15 (by decide) (by omega)).symm]
    exact h1ge15 k (by omega) (fin_ne_of_lt_ge 15 (by decide) (by omega)).symm
  have h3_lt18 : ∀ k : Fin S, k ≠ sW → k ≠ sE2 → k ≠ sQ → k.val < 18 →
      b₃.stacks k = (if 15 ≤ k.val then [] else a.stacks k) := fun k hkw hke hkq hk18 => by
    rw [h3o k hke, h2o k hkw]
    by_cases hk15 : 15 ≤ k.val
    · simp only [hk15, ↓reduceIte]; exact h1ge15 k hk15 hkq
    · simp only [hk15, ↓reduceIte]; exact h1lt15 k (by omega) hkq
  have h3P : b₃.stacks sP = p.bits := by
    rw [h3_lt18 sP (by decide) (by decide) (by decide) (by decide)]; exact hP
  have h3Ans : b₃.stacks sAns = acc.bits := by
    rw [h3_lt18 sAns (by decide) (by decide) (by decide) (by decide)]; exact hAns
  have h3Q : b₃.stacks sQ = v.bits := by rw [h3o sQ (by decide), h2o sQ (by decide), h1Q']
  obtain ⟨n₄, b₄, e₄, hn₄, h4Ans, h4clr18, h4lt18, h4reg⟩ :=
    mulMod_eval (by decide : sAns.val < 18) (by decide : sQ.val < 18)
      (by decide : sP.val < 18) (by decide : sAns.val < 18) b₃
      (by rw [h3P, toNat_bits]; omega) h3clr18
  obtain ⟨n₅, b₅, e₅, hn₅, h5Q, h5o, h5reg⟩ := clearStack_eval sQ b₄
  have h15clr : RangeCleared 15 27 b₅.stacks := by
    intro k hk1 hk2
    rw [h5o k (fin_ne_of_lt_ge 15 (by decide) hk1).symm]
    by_cases hk18 : 18 ≤ k.val
    · exact h4clr18 k hk18 hk2
    · rw [h4lt18 k (by omega) (fin_ne_of_lt_ge 15 (by decide) hk1).symm]
      rw [h3_lt18 k (fin_ne_of_lt_ge 15 (by decide) hk1).symm
        (fin_ne_of_lt_ge 15 (by decide) hk1).symm
        (fin_ne_of_lt_ge 15 (by decide) hk1).symm (by omega)]
      simp [hk1]
  have hn1_bd : n₁ ≤ 130000 * L ^ 3 + 600 := by
    rw [hE2, hW, hP] at hn₁; exact hn₁.trans (powMod_step_bound he2_len hw_len hP_len hQ hL)
  have hn2_bd : n₂ ≤ 3 * L + 2 := by rw [h1lt15 sW (by decide) (by decide), hW] at hn₂; omega
  have hn3_bd : n₃ ≤ 3 * L + 2 := by
    have : b₂.stacks sE2 = e2.bits := by rw [h2o sE2 (by decide), h1lt15 sE2 (by decide) (by decide), hE2]
    rw [this] at hn₃; omega
  have hn4_bd : n₄ ≤ 3000 * L ^ 3 + 3 * L + 200 := by
    rw [h3Ans, h3Q, h3P] at hn₄; exact hn₄.trans (mulMod_step_bound hacc_len hv_len hP_len hacc_len hL)
  have hn5_bd : n₅ ≤ 3 * L + 2 := by
    have : b₄.stacks sQ = v.bits := by rw [h4lt18 sQ (by decide) (by decide), h3Q]
    rw [this] at hn₅; omega
  have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
  refine ⟨_, b₅, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ?_, ?_, ?_, h5Q, h15clr, ?_,
    regPreserved_trans h1reg (regPreserved_trans h2reg (regPreserved_trans h3reg (regPreserved_trans h4reg h5reg)))⟩
  · dsimp only [L] at *; omega
  · rw [h5o sAns (by decide), h4Ans, h3Ans, h3Q, h3P, toNat_bits, toNat_bits, toNat_bits]
  · rw [h5o sW (by decide), h4lt18 sW (by decide) (by decide), h3o sW (by decide), h2W]
  · rw [h5o sE2 (by decide), h4lt18 sE2 (by decide) (by decide), h3E2]
  · intro k hkAns hkW hkE2 hkQ hk15
    rw [h5o k hkQ, h4lt18 k (by omega) hkAns]
    rw [h3_lt18 k hkW hkE2 hkQ (by omega)]
    have : ¬ 15 ≤ k.val := by omega
    simp [this]

theorem scanLoop_eval {p : ℕ} (hp2 : 2 ≤ p) (us : List ℕ) (hus : ∀ u ∈ us, u < p)
    (k acc : ℕ) (curFs : List ℕ) (hlen : curFs.length ≤ k) (hacc : acc < p)
    (hsort : curFs.Pairwise (· ≤ ·))
    (hmem : ∀ y ∈ curFs, 2 ≤ y ∧ y < p ∧ y ^ (curFs.count y) < p)
    (x0 : SState)
    (hHasR : x0.regs rHasR = !curFs.isEmpty)
    (hcur : FactorsHeadMatch x0.stacks curFs)
    (hP : x0.stacks sP = p.bits) (hN : x0.stacks sN = (p - 1).bits)
    (hAns : x0.stacks sAns = acc.bits) (hUs : x0.stacks sUs = encodeNatListBin us)
    (hBak : x0.stacks sUsBak = []) (hRN : x0.stacks sRNext = []) (hRp : x0.stacks sRp = [])
    (hQ : x0.stacks sQ = []) (hE2 : x0.stacks sE2 = []) (hW : x0.stacks sW = [])
    (hU : x0.stacks sU = []) (hIn : x0.stacks sIn = []) (hOut : x0.stacks sOut = [])
    (hclr : RangeCleared 15 27 x0.stacks)
    (hFsLen : (x0.stacks sFs).length ≤ (encodeNatListBin curFs).length + 1) :
    let L := bitLen p + 1
    ∃ n b, StructuredCalls.Eval (mkWhile rHasR scanBody) n x0 b ∧
      n ≤ (curFs.length + 1) * ((us.length + 1) * (140000 * L ^ 3 + 1500) + 4 * (encodeNatListBin us).length + 150000 * L ^ 3 + 5000) + 1 ∧
      b.stacks sAns = (scanIter p acc curFs us).bits ∧
      b.stacks sOut = [] ∧ b.stacks sIn = [] ∧
      b.stacks sFs = [] ∧ b.stacks sUs = encodeNatListBin us ∧
      b.stacks sUsBak = [] ∧ b.stacks sR = [] ∧ b.stacks sRNext = [] ∧ b.stacks sRp = [] ∧
      b.stacks sQ = [] ∧ b.stacks sE2 = [] ∧ b.stacks sW = [] ∧ b.stacks sU = [] ∧
      RangeCleared 15 27 b.stacks ∧
      b.stacks sP = p.bits ∧ b.stacks sN = (p - 1).bits := by
  let L := bitLen p + 1
  have hL : 2 ≤ L := by
    have : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  induction k generalizing acc curFs x0 with
  | zero =>
      cases curFs with
      | nil =>
          simp only [List.isEmpty_nil, Bool.not_true] at hHasR
          dsimp only [FactorsHeadMatch] at hcur
          exact ⟨1, x0, .while_false hHasR, by omega, by simpa [scanIter] using hAns,
            hOut, hIn, hcur.2, hUs, hBak, hcur.1, hRN, hRp, hQ, hE2, hW, hU, hclr, hP, hN⟩
      | cons _ _ => simp at hlen
  | succ k ih =>
      cases curFs with
      | nil =>
          simp only [List.isEmpty_nil, Bool.not_true] at hHasR
          dsimp only [FactorsHeadMatch] at hcur
          exact ⟨1, x0, .while_false hHasR, by omega, by simpa [scanIter] using hAns,
            hOut, hIn, hcur.2, hUs, hBak, hcur.1, hRN, hRp, hQ, hE2, hW, hU, hclr, hP, hN⟩
      | cons r rest =>
          simp only [List.isEmpty_cons, Bool.not_false] at hHasR
          dsimp only [FactorsHeadMatch] at hcur
          have hr_props := hmem r (by simp)
          obtain ⟨n₁, b₁, e₁, hn₁, h1Q, h1E2, h1_hasR, h1tail, h1RN, h1Rp, h1clr, h1o⟩ :=
            scanBodyPre_eval hp2 rest hr_props.1 hr_props.2.1 hsort hmem x0
              hcur.1 hcur.2 hN hRN hRp hQ hE2 hclr
          let q := (p - 1) / r
          let dups := rest.takeWhile (· == r)
          let tail := rest.dropWhile (· == r)
          let rp := r ^ (dups.length + 1)
          let e2 := (p - 1) / rp
          have hq_lt : q < p := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
          have he2_lt : e2 < p := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
          have h1P : b₁.stacks sP = p.bits := (h1o sP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hP
          have h1Us : b₁.stacks sUs = encodeNatListBin us := (h1o sUs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hUs
          have h1Bak : b₁.stacks sUsBak = [] := (h1o sUsBak (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hBak
          have h1W : b₁.stacks sW = [] := (h1o sW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW
          have h1U : b₁.stacks sU = [] := (h1o sU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hU
          obtain ⟨n₂, b₂, sp₂, hn₂, h2Us, h2Bak, h2W, h2U, h2clr, h2o, h2_hasR, _⟩ :=
            firstWitness_spec (B := BitProgram.stackBits b₁.stacks + 150000 * L ^ 3 + 5000)
              hp2 hq_lt us hus b₁ h1P h1Q h1Us h1Bak h1W h1U h1clr le_rfl
          have h2P : b₂.stacks sP = p.bits := (h2o sP (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1P
          have h2Ans : b₂.stacks sAns = acc.bits := (h2o sAns (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((h1o sAns (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hAns)
          have h2E2 : b₂.stacks sE2 = e2.bits := (h2o sE2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1E2
          have h2Q_len : (b₂.stacks sQ).length ≤ L := by
            rw [h2o sQ (by decide) (by decide) (by decide) (by decide) (by decide), h1Q]
            exact lt_prime_bits_length_le hq_lt
          have hfw_lt : firstWitness p q us < p := by
            unfold firstWitness
            cases hf : (us.find? (fun u => decide (powMod p u q ≠ 1))) with
            | none => simpa using (by omega : 1 < p)
            | some u => exact hus u (List.mem_of_find?_eq_some hf)
          obtain ⟨n₃, b₃, e₃, hn₃, h3Ans, h3W, h3E2, h3Q, h3clr, h3o, h3reg⟩ :=
            scanBodyPost_eval hp2 hacc hfw_lt he2_lt b₂ h2P h2Ans h2W h2E2 h2Q_len h2clr
          have hprops := sorted_span_props hsort
          rcases hprops with ⟨_, _, htailSort, hsp, _, _, hcount_other⟩
          have htail_len : tail.length ≤ k := by
            have := List.length_dropWhile_le (p := (· == r)) (l := rest)
            simp only [List.length_cons] at hlen
            dsimp only [tail]
            omega
          have htail_mem : ∀ y ∈ tail, 2 ≤ y ∧ y < p ∧ y ^ (tail.count y) < p := fun y hy => by
            have hyr : y ∈ r :: rest := List.mem_cons_of_mem r (by rw [hsp]; exact List.mem_append_right _ hy)
            have hm := hmem y hyr
            rw [← hcount_other y hy]; exact hm
          let acc' := (acc * powMod p (firstWitness p q us) e2) % p
          have hacc' : acc' < p := Nat.mod_lt _ (by omega)
          have h3_keep : ∀ s : Fin S, s ≠ sAns → s ≠ sW → s ≠ sE2 → s ≠ sQ →
              s ≠ sUs → s ≠ sUsBak → s ≠ sU →
              s ≠ sR → s ≠ sFs → s ≠ sRNext → s ≠ sRp → s.val < 15 →
              b₃.stacks s = x0.stacks s := fun s h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hs15 => by
            rw [h3o s h1 h2 h3 h4 hs15, h2o s h5 h6 h2 h7 hs15, h1o s h8 h9 h10 h11 h4 h3 hs15]
          have h3cur : FactorsHeadMatch b₃.stacks tail := by
            change FactorsHeadMatch b₁.stacks tail at h1tail
            cases htail : tail with
            | nil =>
                rw [htail] at h1tail
                dsimp only [FactorsHeadMatch] at h1tail ⊢
                rw [h3o sR (by decide) (by decide) (by decide) (by decide) (by decide),
                  h2o sR (by decide) (by decide) (by decide) (by decide) (by decide), h1tail.1,
                  h3o sFs (by decide) (by decide) (by decide) (by decide) (by decide),
                  h2o sFs (by decide) (by decide) (by decide) (by decide) (by decide), h1tail.2]
                exact ⟨rfl, rfl⟩
            | cons z zs =>
                rw [htail] at h1tail
                dsimp only [FactorsHeadMatch] at h1tail ⊢
                rw [h3o sR (by decide) (by decide) (by decide) (by decide) (by decide),
                  h2o sR (by decide) (by decide) (by decide) (by decide) (by decide), h1tail.1,
                  h3o sFs (by decide) (by decide) (by decide) (by decide) (by decide),
                  h2o sFs (by decide) (by decide) (by decide) (by decide) (by decide), h1tail.2]
                exact ⟨rfl, rfl⟩
          have h3_hasR : b₃.regs rHasR = !tail.isEmpty := by rw [← h3reg.2.1, h2_hasR, h1_hasR]
          have h3_P : b₃.stacks sP = p.bits := (h3_keep sP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hP
          have h3_N : b₃.stacks sN = (p - 1).bits := (h3_keep sN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
          have h3_Us : b₃.stacks sUs = encodeNatListBin us := by
            rw [h3o sUs (by decide) (by decide) (by decide) (by decide) (by decide), h2Us]
          have h3_Bak : b₃.stacks sUsBak = [] := by
            rw [h3o sUsBak (by decide) (by decide) (by decide) (by decide) (by decide), h2Bak]
          have h3_RN : b₃.stacks sRNext = [] := by
            rw [h3o sRNext (by decide) (by decide) (by decide) (by decide) (by decide),
              h2o sRNext (by decide) (by decide) (by decide) (by decide) (by decide), h1RN]
          have h3_Rp : b₃.stacks sRp = [] := by
            rw [h3o sRp (by decide) (by decide) (by decide) (by decide) (by decide),
              h2o sRp (by decide) (by decide) (by decide) (by decide) (by decide), h1Rp]
          have h3_U : b₃.stacks sU = [] := by
            rw [h3o sU (by decide) (by decide) (by decide) (by decide) (by decide), h2U]
          have h3_In : b₃.stacks sIn = [] := (h3_keep sIn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIn
          have h3_Out : b₃.stacks sOut = [] := (h3_keep sOut (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hOut
          have h3_FsLen : (b₃.stacks sFs).length ≤ (encodeNatListBin tail).length + 1 := by
            cases htail : tail with
            | nil =>
                rw [htail] at h3cur
                dsimp only [FactorsHeadMatch] at h3cur
                simp [h3cur.2]
            | cons z zs =>
                rw [htail] at h3cur
                dsimp only [FactorsHeadMatch] at h3cur
                rw [h3cur.2]
                exact (length_encodeNatListBin_tail_le z zs).trans (Nat.le_succ _)
          obtain ⟨n_tail, fin, e_tail, hn_tail, hfAns, hfOut, hfIn, hfFs, hfUs, hfBak, hfR, hfRN, hfRp, hfQ, hfE2, hfW, hfU, hfclr, hfP, hfN⟩ :=
            ih acc' tail htail_len hacc' htailSort htail_mem b₃ h3_hasR h3cur h3_P h3_N h3Ans
              h3_Us h3_Bak h3_RN h3_Rp h3Q h3E2 h3W h3_U h3_In h3_Out h3clr h3_FsLen
          refine ⟨_, fin, .while_true hHasR (.seq e₁ (.seq sp₂.1 e₃)) e_tail, ?_, ?_,
            hfOut, hfIn, hfFs, hfUs, hfBak, hfR, hfRN, hfRp, hfQ, hfE2, hfW, hfU, hfclr, hfP, hfN⟩
          · let stepCost := (us.length + 1) * (140000 * L ^ 3 + 1500) + 4 * (encodeNatListBin us).length + 150000 * L ^ 3 + 5000
            have h1step : n₁ + (n₂ + n₃) + 1 ≤ stepCost := by
              dsimp only [stepCost, L] at *
              omega
            have htail_le : (tail.length + 1) * stepCost ≤ ((r :: rest).length) * stepCost := by
              apply Nat.mul_le_mul_right
              have := List.length_dropWhile_le (p := (· == r)) (l := rest)
              simp only [List.length_cons]
              dsimp only [tail]
              omega
            have hsum : ((r :: rest).length + 1) * stepCost = (r :: rest).length * stepCost + stepCost := by ring
            change n_tail ≤ (tail.length + 1) * stepCost + 1 at hn_tail
            change (n₁ + (n₂ + n₃)) + n_tail + 1 ≤ ((r :: rest).length + 1) * stepCost + 1
            omega
          · simpa [scanIter] using hfAns

theorem scanLoop_spec {p B : ℕ} (hp2 : 2 ≤ p) (us : List ℕ) (hus : ∀ u ∈ us, u < p)
    (fs : List ℕ) (hsort : fs.Pairwise (· ≤ ·))
    (hmem : ∀ y ∈ fs, 2 ≤ y ∧ y < p ∧ y ^ (fs.count y) < p)
    (a : SState)
    (hHasR : a.regs rHasR = !fs.isEmpty)
    (hcur : FactorsHeadMatch a.stacks fs)
    (hP : a.stacks sP = p.bits) (hN : a.stacks sN = (p - 1).bits)
    (hAns : a.stacks sAns = (1 : ℕ).bits) (hUs : a.stacks sUs = encodeNatListBin us)
    (hBak : a.stacks sUsBak = []) (hRN : a.stacks sRNext = []) (hRp : a.stacks sRp = [])
    (hQ : a.stacks sQ = []) (hE2 : a.stacks sE2 = []) (hW : a.stacks sW = [])
    (hU : a.stacks sU = []) (hIn : a.stacks sIn = []) (hOut : a.stacks sOut = [])
    (hclr : RangeCleared 15 27 a.stacks)
    (hB : (encodeNatListBin fs).length + (encodeNatListBin us).length + 350000 * (bitLen p + 1) ^ 3 + 10000 ≤ B) :
    let L := bitLen p + 1
    ∃ n b, Spec sIn sOut (mkWhile rHasR scanBody) a b n B ∧
      n ≤ (fs.length + 1) * ((us.length + 1) * (140000 * L ^ 3 + 1500) + 4 * (encodeNatListBin us).length + 150000 * L ^ 3 + 5000) + 1 ∧
      b.stacks sAns = (scanIter p 1 fs us).bits ∧
      b.stacks sOut = [] ∧ b.stacks sIn = [] ∧
      b.stacks sFs = [] ∧ b.stacks sUs = encodeNatListBin us ∧
      b.stacks sUsBak = [] ∧ b.stacks sR = [] ∧ b.stacks sRNext = [] ∧ b.stacks sRp = [] ∧
      b.stacks sQ = [] ∧ b.stacks sE2 = [] ∧ b.stacks sW = [] ∧ b.stacks sU = [] ∧
      RangeCleared 15 27 b.stacks ∧
      b.stacks sP = p.bits ∧ b.stacks sN = (p - 1).bits := by
  let L := bitLen p + 1
  have hL : 2 ≤ L := by
    have : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  have haFsLen : (a.stacks sFs).length ≤ (encodeNatListBin fs).length + 1 := by
    cases fs with
    | nil => dsimp only [FactorsHeadMatch] at hcur; simp [hcur.2]
    | cons r rest => dsimp only [FactorsHeadMatch] at hcur; rw [hcur.2]; exact (length_encodeNatListBin_tail_le r rest).trans (Nat.le_succ _)
  obtain ⟨n, b, ev, hn, hAns_f, hOut_f, hIn_f, hFs_f, hUs_f, hBak_f, hR_f, hRN_f, hRp_f, hQ_f, hE2_f, hW_f, hU_f, hclr_f, hP_f, hN_f⟩ :=
    scanLoop_eval hp2 us hus fs.length 1 fs le_rfl (by omega) hsort hmem a hHasR hcur hP hN hAns hUs hBak hRN hRp hQ hE2 hW hU hIn hOut hclr haFsLen
  let fsLen := (encodeNatListBin fs).length
  let usLen := (encodeNatListBin us).length
  let I : SState → Prop := fun x =>
    ∃ (curFs : List ℕ) (acc : ℕ),
      acc < p ∧
      curFs.Pairwise (· ≤ ·) ∧
      (∀ y ∈ curFs, 2 ≤ y ∧ y < p ∧ y ^ (curFs.count y) < p) ∧
      x.regs rHasR = !curFs.isEmpty ∧
      FactorsHeadMatch x.stacks curFs ∧
      x.stacks sP = p.bits ∧ x.stacks sN = (p - 1).bits ∧
      x.stacks sAns = acc.bits ∧ x.stacks sUs = encodeNatListBin us ∧
      x.stacks sUsBak = [] ∧ x.stacks sRNext = [] ∧ x.stacks sRp = [] ∧
      x.stacks sQ = [] ∧ x.stacks sE2 = [] ∧ x.stacks sW = [] ∧ x.stacks sU = [] ∧
      x.stacks sIn = [] ∧ x.stacks sOut = [] ∧
      RangeCleared 15 27 x.stacks ∧
      (x.stacks sFs).length ≤ fsLen
  have hI_bits : ∀ x, I x → BitProgram.stackBits x.stacks ≤ fsLen + usLen + 10 * L := by
    intro x ⟨curFs, acc, hacc, _, hcm, _, hxcur, hxP, hxN, hxAns, hxUs, hxBak, hxRN, hxRp, hxQ, hxE2, hxW, hxU, hxIn, hxOut, hxclr, hxfsLen⟩
    have hxR : (x.stacks sR).length ≤ L := by
      cases curFs with
      | nil => dsimp only [FactorsHeadMatch] at hxcur; simp [hxcur.1]
      | cons r _ => dsimp only [FactorsHeadMatch] at hxcur; rw [hxcur.1]; exact lt_prime_bits_length_le (hcm r (by simp)).2.1
    refine stackBits_data_le x.stacks fsLen usLen L hxIn hxOut hxfsLen
      (by rw [hxUs, hxBak]; simp [usLen])
      (by rw [hxP]; exact prime_bits_length_le hp2)
      (by rw [hxN]; exact lt_prime_bits_length_le (by omega))
      (by rw [hxAns]; exact lt_prime_bits_length_le hacc)
      hxR
      (by rw [hxRN]; simp)
      (by rw [hxRp]; simp)
      (by rw [hxQ]; simp)
      (by rw [hxE2]; simp)
      (by rw [hxW]; simp)
      (by rw [hxU]; simp)
      hxclr
  have hinit : ∀ x, I x → ∀ i, (x.stacks i).length ≤ B := fun x hx i => by
    have hb := hI_bits x hx
    have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
    dsimp only [L] at *
    exact (stackLength_le_stackBits x.stacks i).trans (hb.trans (by omega))
  have hstep : ∀ x, I x → x.regs rHasR = true →
      ∃ m y, Spec sIn sOut scanBody x y m B ∧ I y := by
    intro x hx hxhr
    have hx_bits := hI_bits x hx
    rcases hx with ⟨curFs, acc, hacc, hcsort, hcmem, hxHasR, hxcur, hxP, hxN, hxAns, hxUs, hxBak, hxRN, hxRp, hxQ, hxE2, hxW, hxU, hxIn, hxOut, hxclr, hxfsLen⟩
    cases curFs with
    | nil => simp at hxHasR; rw [hxHasR] at hxhr; cases hxhr
    | cons r rest =>
        dsimp only [FactorsHeadMatch] at hxcur
        have hr_props := hcmem r (by simp)
        obtain ⟨n₁, b₁, e₁, hn₁, h1Q, h1E2, h1_hasR, h1tail, h1RN, h1Rp, h1clr, h1o⟩ :=
          scanBodyPre_eval hp2 rest hr_props.1 hr_props.2.1 hcsort hcmem x
            hxcur.1 hxcur.2 hxN hxRN hxRp hxQ hxE2 hxclr
        have hL3 : L ≤ L ^ 3 := nat_le_cube (by omega)
        have sp₁ : Spec sIn sOut scanBodyPre x b₁ n₁ B :=
          Spec.of_eval_local e₁ (by dsimp only [L] at *; omega)
        let q := (p - 1) / r
        let dups := rest.takeWhile (· == r)
        let tail := rest.dropWhile (· == r)
        let rp := r ^ (dups.length + 1)
        let e2 := (p - 1) / rp
        have hq_lt : q < p := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
        have he2_lt : e2 < p := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
        have h1P : b₁.stacks sP = p.bits := (h1o sP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxP
        have h1N : b₁.stacks sN = (p - 1).bits := (h1o sN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxN
        have h1Ans : b₁.stacks sAns = acc.bits := (h1o sAns (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxAns
        have h1Us : b₁.stacks sUs = encodeNatListBin us := (h1o sUs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxUs
        have h1Bak : b₁.stacks sUsBak = [] := (h1o sUsBak (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxBak
        have h1W : b₁.stacks sW = [] := (h1o sW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxW
        have h1U : b₁.stacks sU = [] := (h1o sU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxU
        have h1In : b₁.stacks sIn = [] := (h1o sIn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxIn
        have h1Out : b₁.stacks sOut = [] := (h1o sOut (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hxOut
        have hprops := sorted_span_props hcsort
        rcases hprops with ⟨_, _, htailSort, hsp, _, _, hcount_other⟩
        have htail_mem : ∀ y ∈ tail, 2 ≤ y ∧ y < p ∧ y ^ (tail.count y) < p := fun y hy => by
          have hyr : y ∈ r :: rest := List.mem_cons_of_mem r (by rw [hsp]; exact List.mem_append_right _ hy)
          have hm := hcmem y hyr
          rw [← hcount_other y hy]; exact hm
        change FactorsHeadMatch b₁.stacks tail at h1tail
        have hb1_fs_len : (b₁.stacks sFs).length ≤ fsLen := by
          cases htail : tail with
          | nil =>
              rw [htail] at h1tail
              dsimp only [FactorsHeadMatch] at h1tail
              simp [h1tail.2]
          | cons z zs =>
              rw [htail] at h1tail
              dsimp only [FactorsHeadMatch] at h1tail
              rw [h1tail.2]
              have hrest_eq : rest = dups ++ z :: zs := by rw [← htail]; exact hsp
              have hzs_le : (encodeNatListBin zs).length ≤ (encodeNatListBin rest).length := by
                rw [hrest_eq, encodeNatListBin_eq_prefix_append, List.length_append]
                have hzs := length_encodeNatListBin_tail_le z zs
                omega
              have hxfs' : (encodeNatListBin rest).length ≤ fsLen := by rw [← hxcur.2]; exact hxfsLen
              exact hzs_le.trans hxfs'
        have hb1_R_len : (b₁.stacks sR).length ≤ L := by
          cases htail : tail with
          | nil =>
              rw [htail] at h1tail
              dsimp only [FactorsHeadMatch] at h1tail
              simp [h1tail.1]
          | cons z zs =>
              rw [htail] at h1tail
              dsimp only [FactorsHeadMatch] at h1tail
              rw [h1tail.1]
              exact lt_prime_bits_length_le (htail_mem z (by rw [htail]; simp)).2.1
        have hb1_bits : BitProgram.stackBits b₁.stacks ≤ fsLen + usLen + 10 * L :=
          stackBits_data_le b₁.stacks fsLen usLen L h1In h1Out hb1_fs_len
            (by rw [h1Us, h1Bak]; simp [usLen])
            (by rw [h1P]; exact prime_bits_length_le hp2)
            (by rw [h1N]; exact lt_prime_bits_length_le (by omega))
            (by rw [h1Ans]; exact lt_prime_bits_length_le hacc)
            hb1_R_len
            (by rw [h1RN]; simp)
            (by rw [h1Rp]; simp)
            (by rw [h1Q]; exact lt_prime_bits_length_le hq_lt)
            (by rw [h1E2]; exact lt_prime_bits_length_le he2_lt)
            (by rw [h1W]; simp)
            (by rw [h1U]; simp)
            h1clr
        obtain ⟨n₂, b₂, sp₂, hn₂, h2Us, h2Bak, h2W, h2U, h2clr, h2o, h2_hasR, _⟩ :=
          firstWitness_spec (B := B) hp2 hq_lt us hus b₁ h1P h1Q h1Us h1Bak h1W h1U h1clr (by dsimp only [L] at *; omega)
        have h2P : b₂.stacks sP = p.bits := (h2o sP (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1P
        have h2N : b₂.stacks sN = (p - 1).bits := (h2o sN (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1N
        have h2Ans : b₂.stacks sAns = acc.bits := (h2o sAns (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1Ans
        have h2E2 : b₂.stacks sE2 = e2.bits := (h2o sE2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1E2
        have h2Q_len : (b₂.stacks sQ).length ≤ L := by
          rw [h2o sQ (by decide) (by decide) (by decide) (by decide) (by decide), h1Q]
          exact lt_prime_bits_length_le hq_lt
        have h2In : b₂.stacks sIn = [] := (h2o sIn (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1In
        have h2Out : b₂.stacks sOut = [] := (h2o sOut (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1Out
        have h2Fs : b₂.stacks sFs = b₁.stacks sFs := h2o sFs (by decide) (by decide) (by decide) (by decide) (by decide)
        have h2R : b₂.stacks sR = b₁.stacks sR := h2o sR (by decide) (by decide) (by decide) (by decide) (by decide)
        have h2RN : b₂.stacks sRNext = b₁.stacks sRNext := h2o sRNext (by decide) (by decide) (by decide) (by decide) (by decide)
        have h2Rp : b₂.stacks sRp = b₁.stacks sRp := h2o sRp (by decide) (by decide) (by decide) (by decide) (by decide)
        have hfw_lt : firstWitness p q us < p := by
          unfold firstWitness
          cases hf : (us.find? (fun u => decide (powMod p u q ≠ 1))) with
          | none => simpa using (by omega : 1 < p)
          | some u => exact hus u (List.mem_of_find?_eq_some hf)
        have hb2_bits : BitProgram.stackBits b₂.stacks ≤ fsLen + usLen + 10 * L :=
          stackBits_data_le b₂.stacks fsLen usLen L h2In h2Out (by rw [h2Fs]; exact hb1_fs_len)
            (by rw [h2Us, h2Bak]; simp [usLen])
            (by rw [h2P]; exact prime_bits_length_le hp2)
            (by rw [h2N]; exact lt_prime_bits_length_le (by omega))
            (by rw [h2Ans]; exact lt_prime_bits_length_le hacc)
            (by rw [h2R]; exact hb1_R_len)
            (by rw [h2RN, h1RN]; simp)
            (by rw [h2Rp, h1Rp]; simp)
            h2Q_len
            (by rw [h2E2]; exact lt_prime_bits_length_le he2_lt)
            (by rw [h2W]; exact lt_prime_bits_length_le hfw_lt)
            (by rw [h2U]; simp)
            h2clr
        obtain ⟨n₃, b₃, e₃, hn₃, h3Ans, h3W, h3E2, h3Q, h3clr, h3o, h3reg⟩ :=
          scanBodyPost_eval hp2 hacc hfw_lt he2_lt b₂ h2P h2Ans h2W h2E2 h2Q_len h2clr
        have sp₃ : Spec sIn sOut scanBodyPost b₂ b₃ n₃ B :=
          Spec.of_eval_local e₃ (by dsimp only [L] at *; omega)
        let acc' := (acc * powMod p (firstWitness p q us) e2) % p
        refine ⟨_, b₃, Spec.seq sp₁ (Spec.seq sp₂ sp₃), tail, acc', Nat.mod_lt _ (by omega), htailSort, htail_mem,
          by rw [← h3reg.2.1, h2_hasR, h1_hasR],
          ?_,
          (h3o sP (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2P,
          (h3o sN (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2N,
          h3Ans,
          (h3o sUs (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2Us,
          (h3o sUsBak (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2Bak,
          (h3o sRNext (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h2RN.trans h1RN),
          (h3o sRp (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h2Rp.trans h1Rp),
          h3Q, h3E2, h3W,
          (h3o sU (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2U,
          (h3o sIn (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2In,
          (h3o sOut (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2Out,
          h3clr,
          by rw [h3o sFs (by decide) (by decide) (by decide) (by decide) (by decide), h2Fs]; exact hb1_fs_len⟩
        cases htail : tail with
        | nil =>
            rw [htail] at h1tail
            dsimp only [FactorsHeadMatch] at h1tail ⊢
            rw [h3o sR (by decide) (by decide) (by decide) (by decide) (by decide), h2R, h1tail.1,
              h3o sFs (by decide) (by decide) (by decide) (by decide) (by decide), h2Fs, h1tail.2]
            exact ⟨rfl, rfl⟩
        | cons z zs =>
            rw [htail] at h1tail
            dsimp only [FactorsHeadMatch] at h1tail ⊢
            rw [h3o sR (by decide) (by decide) (by decide) (by decide) (by decide), h2R, h1tail.1,
              h3o sFs (by decide) (by decide) (by decide) (by decide) (by decide), h2Fs, h1tail.2]
            exact ⟨rfl, rfl⟩
  have hIa : I a := by
    refine ⟨fs, 1, by omega, hsort, hmem, hHasR, hcur, hP, hN, hAns, hUs, hBak, hRN, hRp, hQ, hE2, hW, hU, hIn, hOut, hclr, ?_⟩
    cases fs with
    | nil => dsimp only [FactorsHeadMatch] at hcur; simp [hcur.2]
    | cons r rest => dsimp only [FactorsHeadMatch] at hcur; rw [hcur.2]; exact length_encodeNatListBin_tail_le r rest
  exact ⟨n, b, Spec.while sIn sOut scanBody rHasR I B hinit hstep ev hIa,
    hn, hAns_f, hOut_f, hIn_f, hFs_f, hUs_f, hBak_f, hR_f, hRN_f, hRp_f, hQ_f, hE2_f, hW_f, hU_f, hclr_f, hP_f, hN_f⟩

/-- 22. Output finalizer `finalizeCmd`, complete machine `mainCmd`, and `main_runsWithin`. -/
def finalizeCmd : SCmd :=
  mkSeqList [
    moveStack sAns sOut sTmp1,
    mkAtom (.peek sOut rTmp1 rFlag),
    mkAtom (.bnot rFlag rFlag),
    mkIte rFlag (mkSeqList [mkAtom (.set rBit false), mkAtom (.push sOut rBit)]) mkSkip
  ]

theorem finalize_eval (x : ℕ) (a : SState)
    (hAns : a.stacks sAns = x.bits) (hOut : a.stacks sOut = []) (ht1 : a.stacks sTmp1 = []) :
    ∃ n b, StructuredCalls.Eval finalizeCmd n a b ∧
      n ≤ 8 * x.bits.length + 12 ∧
      b.stacks sOut = countWord x := by
  obtain ⟨n₁, b₁, e₁, hn₁, _, h1Out, _, _⟩ :=
    moveStack_eval (by decide : sAns ≠ sOut) (by decide : sAns ≠ sTmp1) (by decide : sOut ≠ sTmp1) a ht1
  have h1Out' : b₁.stacks sOut = x.bits := by rw [h1Out, hAns]
  let b₂ : SState := ⟨BitProgram.readRegs b₁.regs rTmp1 rFlag (b₁.stacks sOut).head?, b₁.stacks⟩
  have e₂ := eval_peek b₁ sOut rTmp1 rFlag
  let b₃ : SState := ⟨Function.update b₂.regs rFlag (!(b₂.regs rFlag)), b₂.stacks⟩
  have e₃ := eval_bnot b₂ rFlag rFlag
  have hb3_flag : b₃.regs rFlag = x.bits.isEmpty := by
    dsimp only [b₃, b₂]; rw [Function.update_self, readRegs_eq_pres, h1Out']
    cases x.bits <;> rfl
  have hn1_bd : n₁ ≤ 8 * x.bits.length + 6 := by rw [hOut, hAns] at hn₁; simp only [List.length_nil] at hn₁; omega
  cases hxb : x.bits.isEmpty with
  | true =>
      have ht3 : b₃.regs rFlag = true := by rw [hb3_flag, hxb]
      let b₄ : SState := ⟨Function.update b₃.regs rBit false, b₃.stacks⟩
      have e₄ := eval_set b₃ rBit false
      let b₅ : SState := ⟨b₄.regs, Function.update b₄.stacks sOut (false :: b₄.stacks sOut)⟩
      have e₅ : StructuredCalls.Eval (mkAtom (.push sOut rBit)) 1 b₄ b₅ := by
        simpa [b₅, b₄] using eval_push b₄ sOut rBit
      refine ⟨_, b₅, .seq e₁ (.seq e₂ (.seq e₃ (.ite_true ht3 (.seq e₄ e₅)))), by omega, ?_⟩
      dsimp only [b₅, b₄, b₃, b₂]; rw [Function.update_self, h1Out']
      rw [← bits_ite_zero x, hxb]
      cases hxs : x.bits with
      | nil => rfl
      | cons _ _ => simp [hxs] at hxb
  | false =>
      have hf3 : b₃.regs rFlag = false := by rw [hb3_flag, hxb]
      refine ⟨_, b₃, .seq e₁ (.seq e₂ (.seq e₃ (.ite_false hf3 (.base (.skip b₃))))), by omega, ?_⟩
      dsimp only [b₃, b₂]; rw [h1Out', ← bits_ite_zero x, hxb]; rfl

def mainCmd : SCmd :=
  mkSeqList [
    unpackCmd,
    popNatFrame sFs sR sTmp1 rHasR,
    mkWhile rHasR scanBody,
    finalizeCmd
  ]

theorem popNatFrame_fs_eval (xs : List ℕ) (a : SState)
    (hsrc : a.stacks sFs = encodeNatListBin xs) (htmp : a.stacks sTmp1 = [])
    (hdst0 : a.stacks sR = [])
    {L : ℕ} (hL : 2 ≤ L) (hxs : ∀ x ∈ xs, (countWord x).length ≤ L) :
    ∃ n b, StructuredCalls.Eval (popNatFrame sFs sR sTmp1 rHasR) n a b ∧
      n ≤ 25 * L + 25 ∧
      b.regs rHasR = !xs.isEmpty ∧
      FactorsHeadMatch b.stacks xs ∧
      b.stacks sTmp1 = [] ∧
      (∀ k, k ≠ sFs → k ≠ sR → k ≠ sTmp1 → b.stacks k = a.stacks k) := by
  obtain ⟨n, b, e, hn, hs, hd, ht, ho, hf, _, _, _⟩ :=
    popNatFrame_eval (by decide : sFs ≠ sR) (by decide : sFs ≠ sTmp1) (by decide : sR ≠ sTmp1)
      rHasR (by decide) (Or.inl rfl) xs a hsrc htmp
  cases xs with
  | nil =>
      simp only [List.isEmpty_nil, Bool.not_true] at hn hs hd hf
      rw [hdst0, List.length_nil] at hn
      exact ⟨n, b, e, by omega, hf, ⟨hd, hs⟩, ht, ho⟩
  | cons r rest =>
      simp only [List.isEmpty_cons, Bool.not_false] at hn hs hd hf
      rw [hdst0, List.length_nil] at hn
      have hcw := hxs r (by simp)
      exact ⟨n, b, e, by omega, hf, ⟨hd, hs⟩, ht, ho⟩

theorem main_runsWithin :
    ∃ (K : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (U : List (ZMod p)ˣ),
        let us := U.map M89Scan.unitRep
        let fs := (p - 1).primeFactorsList
        let input := Encoding.encodeList id [countWord p, encodeNatListBin fs, encodeNatListBin us]
        RunsWithin (GuardedCompiler.primitive (StructuredCalls.compiled mainCmd sIn sOut)) sOut
          input (countWord (M89Scan.scan p fs us))
          (polyBound K (bitLen p) * (U.length + 1 : ℝ))
          (polyBound K (bitLen p) + K * (input.length + 1 : ℝ)) := by
  refine ⟨10000000, fun p _ U => ?_⟩
  let us := U.map M89Scan.unitRep
  let fs := (p - 1).primeFactorsList
  let input := Encoding.encodeList id [countWord p, encodeNatListBin fs, encodeNatListBin us]
  let L := bitLen p + 1
  have ⟨hp2, hfs_len, hfs_mem, hfs_pow, hfs_sort⟩ := primeFactorsList_props (p := p)
  have hL : 2 ≤ L := by
    have : 1 ≤ bitLen p := Nat.clog_pos (by decide) (by omega)
    omega
  have hus_lt : ∀ u ∈ us, u < p := by
    intro u hu
    rcases List.mem_map.mp hu with ⟨u', _, rfl⟩
    exact ZMod.val_lt (u' : ZMod p)
  have hfs_full : ∀ y ∈ fs, 2 ≤ y ∧ y < p ∧ y ^ (fs.count y) < p := fun y hy =>
    ⟨(hfs_mem y hy).1, (hfs_mem y hy).2, (hfs_pow y hy).2⟩
  have hus_len : us.length = U.length := List.length_map _
  have hinput_len : input.length ≤ 14 * L ^ 2 * (U.length + 1) := by
    change input.length ≤ 14 * (bitLen p + 1) ^ 2 * (U.length + 1)
    exact input_length_le U
  have hlen_decomp : input.length = 2 * (countWord p).length + 2 * (encodeNatListBin fs).length +
      2 * (encodeNatListBin us).length + 7 := by
    simp [input, Encoding.encodeList, frame_length]; omega
  let B_global := input.length + 350000 * L ^ 3 + 10000
  let B_unpack := input.length + 70 * L + 160
  have hB_le : B_unpack ≤ B_global := by
    have : L ≤ L ^ 3 := nat_le_cube (by omega)
    dsimp only [B_unpack, B_global, L] at *
    omega
  -- Stage 1: unpackCmd
  obtain ⟨n₁, a₁, sp₁_raw, hn₁, h1P, h1N, h1Ans, h1Fs, h1Us, h1zero⟩ := unpack_spec hp2 fs us
  have sp₁ : Spec sIn sOut unpackCmd (StructuredProgram.ioState sIn input) a₁ n₁ B_global :=
    Spec.mono sp₁_raw hB_le
  -- Stage 2: popNatFrame sFs sR sTmp1 rHasR
  obtain ⟨n₂, a₂, e₂, hn2_bd, h2_hasR, h2cur, h2t1, h2o⟩ :=
    popNatFrame_fs_eval fs a₁ h1Fs
      (h1zero sTmp1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (h1zero sR (by decide) (by decide) (by decide) (by decide) (by decide))
      hL (fun r hr => (countWord_length_le r).trans (max_le (by omega) (lt_prime_bits_length_le (hfs_mem r hr).2)))
  have ha1_bits : BitProgram.stackBits a₁.stacks ≤ (encodeNatListBin fs).length + (encodeNatListBin us).length + 10 * L := by
    refine stackBits_data_le a₁.stacks (encodeNatListBin fs).length (encodeNatListBin us).length L
      (h1zero sIn (by decide) (by decide) (by decide) (by decide) (by decide))
      (h1zero sOut (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [h1Fs])
      (by rw [h1Us, h1zero sUsBak (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
      (by rw [h1P]; exact prime_bits_length_le hp2)
      (by rw [h1N]; exact lt_prime_bits_length_le (by omega))
      (by rw [h1Ans]; simp only [List.length_singleton]; omega)
      (by rw [h1zero sR (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
      (by rw [h1zero sRNext (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
      (by rw [h1zero sRp (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
      (by rw [h1zero sQ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
      (by rw [h1zero sE2 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
      (by rw [h1zero sW (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
      (by rw [h1zero sU (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
      (fun k hk1 _ => h1zero k (fin_ne_of_lt_ge 15 (by decide) hk1).symm
        (fin_ne_of_lt_ge 15 (by decide) hk1).symm (fin_ne_of_lt_ge 15 (by decide) hk1).symm
        (fin_ne_of_lt_ge 15 (by decide) hk1).symm (fin_ne_of_lt_ge 15 (by decide) hk1).symm)
  have hL3 : 100 * L ≤ 100 * L ^ 3 := Nat.mul_le_mul_left 100 (nat_le_cube (by omega))
  have sp₂ : Spec sIn sOut (popNatFrame sFs sR sTmp1 rHasR) a₁ a₂ n₂ B_global :=
    Spec.of_eval_local e₂ (by dsimp only [B_global, L] at *; omega)
  -- Stage 3: scanLoop_spec
  have h2clr : RangeCleared 15 27 a₂.stacks := fun k hk1 _ => by
    by_cases hkt1 : k = sTmp1
    · subst hkt1; exact h2t1
    · rw [h2o k (fin_ne_of_lt_ge 15 (by decide) hk1).symm (fin_ne_of_lt_ge 15 (by decide) hk1).symm hkt1]
      exact h1zero k (fin_ne_of_lt_ge 15 (by decide) hk1).symm
        (fin_ne_of_lt_ge 15 (by decide) hk1).symm (fin_ne_of_lt_ge 15 (by decide) hk1).symm
        (fin_ne_of_lt_ge 15 (by decide) hk1).symm (fin_ne_of_lt_ge 15 (by decide) hk1).symm
  have h2_keep : ∀ k : Fin S, k ≠ sFs → k ≠ sR → k.val < 15 → a₂.stacks k = a₁.stacks k := fun k h1 h2 hk15 =>
    h2o k h1 h2 (fin_ne_of_lt_ge 15 hk15 (by decide))
  obtain ⟨n₃, a₃, sp₃, hn₃, h3Ans, h3Out, h3In, h3Fs, h3Us, h3Bak, h3R, h3RN, h3Rp, h3Q, h3E2, h3W, h3U, h3clr, h3P, h3N⟩ :=
    scanLoop_spec (B := B_global) hp2 us hus_lt fs hfs_sort hfs_full a₂ h2_hasR h2cur
      ((h2_keep sP (by decide) (by decide) (by decide)).trans h1P)
      ((h2_keep sN (by decide) (by decide) (by decide)).trans h1N)
      ((h2_keep sAns (by decide) (by decide) (by decide)).trans h1Ans)
      ((h2_keep sUs (by decide) (by decide) (by decide)).trans h1Us)
      ((h2_keep sUsBak (by decide) (by decide) (by decide)).trans (h1zero sUsBak (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((h2_keep sRNext (by decide) (by decide) (by decide)).trans (h1zero sRNext (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((h2_keep sRp (by decide) (by decide) (by decide)).trans (h1zero sRp (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((h2_keep sQ (by decide) (by decide) (by decide)).trans (h1zero sQ (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((h2_keep sE2 (by decide) (by decide) (by decide)).trans (h1zero sE2 (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((h2_keep sW (by decide) (by decide) (by decide)).trans (h1zero sW (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((h2_keep sU (by decide) (by decide) (by decide)).trans (h1zero sU (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((h2_keep sIn (by decide) (by decide) (by decide)).trans (h1zero sIn (by decide) (by decide) (by decide) (by decide) (by decide)))
      ((h2_keep sOut (by decide) (by decide) (by decide)).trans (h1zero sOut (by decide) (by decide) (by decide) (by decide) (by decide)))
      h2clr (by dsimp only [B_global, L] at *; omega)
  -- Stage 4: finalizeCmd
  have hscan_eq : scanIter p 1 fs us = scan p fs us := scanIter_eq_scan hp2 fs us hfs_sort
  have hscan_lt : scan p fs us < p := by
    simp only [scan, residueProduct_eq_prod_mod]
    exact Nat.mod_lt _ (by omega)
  rw [hscan_eq] at h3Ans
  obtain ⟨n₄, a₄, e₄, hn₄, h4Out⟩ := finalize_eval (scan p fs us) a₃ h3Ans h3Out (h3clr sTmp1 (by decide) (by decide))
  have ha3_bits : BitProgram.stackBits a₃.stacks ≤ (encodeNatListBin us).length + 10 * L := by
    simpa only [Nat.zero_add] using stackBits_data_le a₃.stacks 0 (encodeNatListBin us).length L h3In h3Out
      (by rw [h3Fs]; simp)
      (by rw [h3Us, h3Bak]; simp)
      (by rw [h3P]; exact prime_bits_length_le hp2)
      (by rw [h3N]; exact lt_prime_bits_length_le (by omega))
      (by rw [h3Ans]; exact lt_prime_bits_length_le hscan_lt)
      (by rw [h3R]; simp)
      (by rw [h3RN]; simp)
      (by rw [h3Rp]; simp)
      (by rw [h3Q]; simp)
      (by rw [h3E2]; simp)
      (by rw [h3W]; simp)
      (by rw [h3U]; simp)
      h3clr
  have hscan_len : (scan p fs us).bits.length ≤ L := lt_prime_bits_length_le hscan_lt
  have sp₄ : Spec sIn sOut finalizeCmd a₃ a₄ n₄ B_global :=
    Spec.of_eval_local e₄ (by dsimp only [B_global, L] at *; omega)
  have sp_all : Spec sIn sOut mainCmd (StructuredProgram.ioState sIn input) a₄ (n₁ + (n₂ + (n₃ + n₄))) B_global :=
    Spec.seq sp₁ (Spec.seq sp₂ (Spec.seq sp₃ sp₄))
  -- Polynomial time & space bounds
  have hLK4 : L ^ 4 ≤ L ^ 10000000 := Nat.pow_le_pow_right (by omega) (by decide)
  have hLK3 : L ^ 3 ≤ L ^ 10000000 := Nat.pow_le_pow_right (by omega) (by decide)
  have hcube8 : 8 ≤ L ^ 3 := nat_cube_ge8 hL
  have h2L2_L3 : 2 * L ^ 2 ≤ L ^ 3 := nat_two_mul_sq_le_cube hL
  have h4L2_L4 : 4 * L ^ 2 ≤ L ^ 4 := nat_four_mul_sq_le_pow4 hL
  have h8L_L4 : 8 * L ≤ L ^ 4 := nat_eight_mul_le_pow4 hL
  have hpow4_16 : 16 ≤ L ^ 4 := nat_pow4_ge16 hL
  have ht_nat : 7 * ((n₁ + (n₂ + (n₃ + n₄))) + 1) ≤ 10000000 * L ^ 10000000 * (U.length + 1) := by
    have hus_enc_le : (encodeNatListBin us).length ≤ 14 * L ^ 2 * (U.length + 1) := by
      have : (encodeNatListBin us).length ≤ input.length := by omega
      exact this.trans hinput_len
    have hpow_step1 : 140000 * L ^ 3 + 1500 ≤ 141000 * L ^ 3 := by omega
    have hpow_step2 : 150000 * L ^ 3 + 5000 ≤ 151000 * L ^ 3 := by omega
    have hL2_L3_56 : 56 * L ^ 2 ≤ 28 * L ^ 3 := by omega
    let stepCost := (us.length + 1) * (140000 * L ^ 3 + 1500) + 4 * (encodeNatListBin us).length + 150000 * L ^ 3 + 5000
    have hstep_bd : stepCost ≤ 300000 * L ^ 3 * (U.length + 1) := by
      dsimp only [stepCost]
      have ha1 : (us.length + 1) * (140000 * L ^ 3 + 1500) ≤ (U.length + 1) * (141000 * L ^ 3) := by
        rw [hus_len]; exact Nat.mul_le_mul_left (U.length + 1) hpow_step1
      have ha2 : 4 * (encodeNatListBin us).length ≤ 56 * L ^ 2 * (U.length + 1) := by
        have h4u := Nat.mul_le_mul_left 4 hus_enc_le
        have h4eq : 4 * (14 * L ^ 2 * (U.length + 1)) = 56 * L ^ 2 * (U.length + 1) := by ring
        exact h4u.trans_eq h4eq
      have ha3 : 56 * L ^ 2 * (U.length + 1) ≤ 28 * L ^ 3 * (U.length + 1) :=
        Nat.mul_le_mul_right (U.length + 1) hL2_L3_56
      have hb1 : 150000 * L ^ 3 + 5000 ≤ 151000 * L ^ 3 * (U.length + 1) :=
        hpow_step2.trans (Nat.le_mul_of_pos_right _ (by omega))
      have hsum_eq : (U.length + 1) * (141000 * L ^ 3) + 28 * L ^ 3 * (U.length + 1) +
          151000 * L ^ 3 * (U.length + 1) = 292028 * (L ^ 3 * (U.length + 1)) := by ring
      have hmul_le : 292028 * (L ^ 3 * (U.length + 1)) ≤ 300000 * L ^ 3 * (U.length + 1) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega
    have hn3_bd : n₃ ≤ 300000 * L ^ 4 * (U.length + 1) + 1 := by
      have hmul1 : (fs.length + 1) * stepCost ≤ L * (300000 * L ^ 3 * (U.length + 1)) :=
        Nat.mul_le_mul (by dsimp only [L, fs] at *; omega) hstep_bd
      have hmul2 : L * (300000 * L ^ 3 * (U.length + 1)) = 300000 * L ^ 4 * (U.length + 1) := by ring
      dsimp only [stepCost, L] at *
      omega
    have hn1_bd : n₁ ≤ 200 * L ^ 4 * (U.length + 1) := by
      have hn1' : n₁ ≤ 10 * input.length + 70 * L + 160 := hn₁
      have h14 : 10 * input.length ≤ 140 * L ^ 2 * (U.length + 1) := by
        have h10 := Nat.mul_le_mul_left 10 hinput_len
        have h10eq : 10 * (14 * L ^ 2 * (U.length + 1)) = 140 * L ^ 2 * (U.length + 1) := by ring
        exact h10.trans_eq h10eq
      have hL24 : 140 * L ^ 2 ≤ 40 * L ^ 4 := by omega
      have hL14 : 70 * L + 160 ≤ 40 * L ^ 4 := by omega
      have ha : 140 * L ^ 2 * (U.length + 1) ≤ 40 * L ^ 4 * (U.length + 1) := Nat.mul_le_mul_right _ hL24
      have hb : 40 * L ^ 4 ≤ 40 * L ^ 4 * (U.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have h80 : 40 * L ^ 4 * (U.length + 1) + 40 * L ^ 4 * (U.length + 1) ≤ 200 * L ^ 4 * (U.length + 1) := by
        have hlin : 40 * L ^ 4 * (U.length + 1) + 40 * L ^ 4 * (U.length + 1) = 80 * (L ^ 4 * (U.length + 1)) := by ring
        rw [hlin, Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega
    have hn24_bd : n₂ + n₄ + 2 ≤ 100 * L ^ 4 * (U.length + 1) := by
      have h24_sum : n₂ + n₄ + 2 ≤ 33 * L + 39 := by dsimp only [L] at *; omega
      have h33 : 33 * L + 39 ≤ 100 * L ^ 4 := by omega
      have h100 : 100 * L ^ 4 ≤ 100 * L ^ 4 * (U.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have htotal : 7 * ((n₁ + (n₂ + (n₃ + n₄))) + 1) ≤ 10000000 * L ^ 4 * (U.length + 1) := by
      rw [Nat.mul_assoc] at hn3_bd hn1_bd hn24_bd ⊢
      omega
    exact htotal.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hLK4))
  have hs_nat : S * (B_global + input.length + 15) ≤ 10000000 * L ^ 10000000 + 10000000 * (input.length + 1) := by
    have h28 : S * (B_global + input.length + 15) = 56 * input.length + 9800000 * L ^ 3 + 280420 := by
      dsimp only [S, B_global]; ring
    have hconst : 280420 ≤ 200000 * L ^ 3 := by omega
    have hc2 : 9800000 * L ^ 3 + 280420 ≤ 10000000 * L ^ 10000000 := by
      have : 9800000 * L ^ 3 + 280420 ≤ 10000000 * L ^ 3 := by omega
      exact this.trans (Nat.mul_le_mul_left _ hLK3)
    omega
  refine Spec.to_runsWithin sp_all h4Out ?_ ?_
  · calc
      ((7 * ((n₁ + (n₂ + (n₃ + n₄))) + 1) : ℕ) : ℝ)
          ≤ ((10000000 * L ^ 10000000 * (U.length + 1) : ℕ) : ℝ) := by exact_mod_cast ht_nat
      _ = polyBound 10000000 (bitLen p) * (U.length + 1 : ℝ) := by
          simp only [polyBound, L, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
  · calc
      ((S * (B_global + input.length + 15) : ℕ) : ℝ)
          ≤ ((10000000 * L ^ 10000000 + 10000000 * (input.length + 1) : ℕ) : ℝ) := by exact_mod_cast hs_nat
      _ = polyBound 10000000 (bitLen p) + 10000000 * (input.length + 1 : ℝ) := by
          simp only [polyBound, L, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]

end ScanKernel

end DetDLP.M89ScanKernel

open DetDLP DetDLP.M89ScanKernel OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (U : List (ZMod p)ˣ),
        let us := U.map M89Scan.unitRep
        let fs := (p-1).primeFactorsList
        let input := Encoding.encodeList id [countWord p, encodeNatListBin fs, encodeNatListBin us]
        RunsWithin M out input (countWord (M89Scan.scan p fs us))
          (polyBound K (bitLen p) * (U.length + 1 : ℝ))
          (polyBound K (bitLen p) + K * (input.length + 1 : ℝ)) := by
  obtain ⟨K, hK⟩ := main_runsWithin
  exact ⟨GuardedCompiler.primitive (StructuredCalls.compiled mainCmd sIn sOut), sOut, K, hK⟩





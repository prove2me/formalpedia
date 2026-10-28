-- Prove2me | solution 1 for BitDFT.precision_program_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:40:14.33757+00:00
-- url     : https://prove2.me/submissions/9a1b16c0-d8a2-4192-9be8-d347c5fb74e7

import Definitions.Def_BitDFT_PrecisionProgram
import Definitions.Def_BitDFT_Numerics
import Theorems.Thm_BitDFT_log_scanner_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Theorems.Thm_BitDFT_machine_sequence_bound
import Theorems.Thm_BitDFT_binary_counter_add_bounded

namespace BitDFT.PrecisionProgram
open IntMul
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

/-- The routed scanner leaves exactly the physical layout required by the counter. -/
theorem handoff_correct (base : arithmetic.Cfg) (tail w : List Bool) :
    MachineSequence.handoff scanControl (MachineSequence.native arithmetic) (scanFinished base tail w) =
      counterInitial base tail w := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [MachineSequence.handoff,scanFinished,counterInitial,
      TapePermutation.embed,TapeExtension.embed,LogScanner.frame,BinaryCounter.frame,
      base4,counterBase4,swap24,Equiv.swap_apply_def,TapeExtension.oldTape] <;> rfl
  · funext i
    fin_cases i <;> simp [MachineSequence.handoff,scanFinished,counterInitial,
      TapePermutation.embed,TapeExtension.embed,LogScanner.frame,BinaryCounter.frame,
      base4,counterBase4,swap24,Equiv.swap_apply_def,TapeExtension.oldTape] <;> rfl


theorem scanner_run (base : arithmetic.Cfg) (tail w : List Bool) :
    let k := 3*IntMul.lg (IntMul.val (true::tail))+5
    scanControl.machine.step^[k+3] (scanInitial base tail w) = scanFinished base tail w := by
  dsimp only
  change scanRouted.step^[_] _ = _
  unfold scanInitial scanFinished
  rw [BitDFT.tape_permutation_run,(BitDFT.tape_extension_correct LogScanner.machine 1).1,
    BitDFT.log_scanner_correct]

private theorem counter_run (base : arithmetic.Cfg) (tail w v : List Bool) (u : ℕ)
    (h : BinaryCounter.machine.step^[u]
      (BinaryCounter.frame (counterBase4 base) .tick w.reverse (3*IntMul.lg (IntMul.val (true::tail))+5) 1) =
      BinaryCounter.frame (counterBase4 base) .halt v 0 1) :
    arithmetic.step^[u] (counterInitial base tail w) = finalArithmetic base tail v := by
  unfold counterInitial
  rw [(BitDFT.tape_extension_correct BinaryCounter.machine 1).1,h]
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeExtension.embed,BinaryCounter.frame,finalArithmetic,counterBase4,
      TapeExtension.oldTape] <;> rfl
  · funext i
    fin_cases i <;> simp [TapeExtension.embed,BinaryCounter.frame,finalArithmetic,counterBase4,
      TapeExtension.oldTape]


private theorem reverse_value (w : List Bool) : BinaryCounter.value w.reverse = IntMul.val w := by
  have happ : ∀ a : List Bool, ∀ b : Bool, IntMul.val (a++[b]) = 2*IntMul.val a+b.toNat := by
    intro a b
    simp [IntMul.val,List.foldl_append]
  suffices h : ∀ a : List Bool, BinaryCounter.value a = IntMul.val a.reverse by
    simpa using h w.reverse
  intro a
  induction a with
  | nil => rfl
  | cons b a ih =>
    rw [List.reverse_cons,happ]
    simp only [BinaryCounter.value,ih]
    omega

end BitDFT.PrecisionProgram

open BitDFT BitDFT.PrecisionProgram IntMul

/-- Complete scanner/counter composition: the unary operand is constructed, not assumed. -/
theorem solution (base : arithmetic.Cfg) (tail w : List Bool)
    (hb : 1 ≤ IntMul.val w) (hw : w.length ≤ IntMul.val w) :
    let q := BitDFT.guardPrecision (IntMul.val (true::tail)) (IntMul.val w)
    ∃ t v, t ≤ 7*q ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (initial base tail w) = final base tail v := by
  dsimp only
  let n := IntMul.val (true::tail)
  let b := IntMul.val w
  let k := 3*IntMul.lg n+5
  let q := BitDFT.guardPrecision n b
  obtain ⟨u,v,hu,hv,hlen,hr⟩ := BitDFT.binary_counter_add_bounded (counterBase4 base) w.reverse k
  have hvq : BinaryCounter.value v = q := by
    rw [reverse_value] at hv
    simpa [q,BitDFT.guardPrecision,k,b,Nat.add_assoc] using hv
  have hlenq : v.length ≤ q := by
    simp only [List.length_reverse] at hlen
    dsimp [q,BitDFT.guardPrecision,k,b] at hlen ⊢
    omega
  have hs : scanControl.machine.step^[k+3] (scanInitial base tail w) = scanFinished base tail w :=
    scanner_run base tail w
  have hh : (scanControl.machine.step^[k+3] (scanInitial base tail w)).state = scanControl.exit := by
    rw [hs]
    rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound scanControl (MachineSequence.native arithmetic)
    (scanInitial base tail w) (k+3) u hh
  rw [hs,handoff_correct] at he
  change machine.step^[t] (initial base tail w) =
    MachineSequence.rightCfg scanControl (MachineSequence.native arithmetic)
      (arithmetic.step^[u] (counterInitial base tail w)) at he
  rw [counter_run base tail w v u hr] at he
  refine ⟨t,v,?_,hvq,hlenq,he⟩
  change t ≤ 7*q
  simp only [List.length_reverse] at hu
  dsimp [q,BitDFT.guardPrecision,k,b] at hu ht ⊢
  omega


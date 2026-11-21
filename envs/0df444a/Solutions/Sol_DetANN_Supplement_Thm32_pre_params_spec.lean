-- Prove2me | solution 1 for DetANN.Supplement.Thm32.pre_params_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-21T03:40:52.172984+00:00
-- url     : https://prove2.me/submissions/04b98216-33b7-43dd-a993-fde5e349e3fc

import Mathlib
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_Supplement_PreDedup
import Definitions.Def_DetANN_SignedBlocks

namespace DetANN.HPIM.QP
end DetANN.HPIM.QP
namespace DetANN.HPIM
end DetANN.HPIM
namespace DetANN.HPIM.PP
end DetANN.HPIM.PP
namespace DetANN.HPIM.SegStep
end DetANN.HPIM.SegStep

-- ===== QP_Work =====
open PNormReg PNormRegLib SmaleNinth

namespace DetANN.HPIM.QP

lemma RAMStep_eq {R : RAMProgram} {s : RAMConfig} {i : RAMInstr} (h : R[s.pc]? = some i) :
    RAMStep R s = coreExec i s := by
  simp only [RAMStep, h]
  cases i <;> rfl

lemma core_get {P : Program} {pc : ℕ} {i : RAMInstr} (h : P[pc]? = some (.core i)) :
    (coreProgram P)[pc]? = some i := by
  simp [coreProgram, List.getElem?_map, h]

lemma step_eq_exec (P : Program) (ω : ℕ → Bool) (s : State) (ins : Instr)
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) : step P ω s = exec ω ins s := by
  cases ins with
  | core i => simp [step, exec, hh, h, RAMStep_eq (core_get h)]
  | _ => simp [step, exec, hh, h]

lemma run_succ (P : Program) (s : State) (ω : ℕ → Bool) (n : ℕ) :
    run P s ω (n + 1) = run P (step P ω s) ω n := by
  simp [run, Function.iterate_succ_apply]

lemma run_zero (P : Program) (s : State) (ω : ℕ → Bool) : run P s ω 0 = s := rfl

lemma run_add (P : Program) (s : State) (ω : ℕ → Bool) (a b : ℕ) :
    run P s ω (a + b) = run P (run P s ω a) ω b := by
  simp only [run]; rw [add_comm, Function.iterate_add_apply]

lemma run_exec {P : Program} {s : State} {ω : ℕ → Bool} {n : ℕ} {ins : Instr}
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) :
    run P s ω (n + 1) = run P (exec ω ins s) ω n := by
  rw [run_succ, step_eq_exec P ω s ins hh h]

end DetANN.HPIM.QP

-- ===== PP_Ladder =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP

/-- One step of a host `Q` through instruction `i` of an embedded block. -/
lemma run_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {ω : ℕ → Bool} {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i)
    (hB : B[i]? = some ins) : run Q s ω (n + 1) = run Q (exec ω ins s) ω n :=
  run_exec hh (by rw [hpc]; exact hE i ins hB)

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib DetANN.HPIM.QP

end DetANN.HPIM.PP

-- ===== PP_Basic =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN

/-- `cellsWritten` over consecutive run segments. -/
lemma cellsWritten_add (P : Program) (s : State) (a b : ℕ) :
    cellsWritten P s (a + b) = cellsWritten P s a ∪ cellsWritten P (run P s detTape a) b := by
  ext c
  simp only [cellsWritten, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hc⟩
    by_cases hia : i < a
    · exact Or.inl ⟨i, hia, hc⟩
    · refine Or.inr ⟨i - a, by omega, ?_⟩
      rw [← run_add, Nat.add_sub_cancel' (by omega)]; exact hc
  · rintro (⟨i, hi, hc⟩ | ⟨i, hi, hc⟩)
    · exact ⟨i, by omega, hc⟩
    · exact ⟨a + i, by omega, by rw [run_add]; exact hc⟩

lemma cellsWritten_zero (P : Program) (s : State) : cellsWritten P s 0 = ∅ := by
  simp [cellsWritten]

end DetANN.HPIM.PP

-- ===== PP_Step =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The cell stored to by instruction `ins` in state `s`. -/
def wcell (ins : Instr) (s : State) : Option (Bool × ℤ) :=
  match ins with
  | .core (.store q _) => some (true, s.core.ptrs q)
  | .integerStore a _ => some (false, s.core.ptrs a)
  | _ => none

lemma cw_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i) (hB : B[i]? = some ins) :
    cellsWritten Q s (n + 1) = (wcell ins s).toFinset ∪ cellsWritten Q (exec detTape ins s) n := by
  have hQ : Q[s.core.pc]? = some ins := by rw [hpc]; exact hE i ins hB
  rw [show n + 1 = 1 + n by omega, cellsWritten_add]
  congr 1
  · simp only [cellsWritten, Finset.range_one, Finset.singleton_biUnion, run_zero, writtenCell, hh,
      Bool.false_eq_true, if_false, hQ]
    cases ins with
    | core i => cases i <;> rfl
    | _ => rfl
  · rw [run_succ, run_zero, step_eq_exec Q detTape s ins hh hQ]

lemma cw_zero (Q : Program) (s : State) : cellsWritten Q s 0 = ∅ := cellsWritten_zero Q s

end DetANN.HPIM.PP

-- ===== SegStep =====
namespace DetANN.HPIM.SegStep

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP

lemma embeds_app_right {Q A B : Program} {o : ℕ} (h : Embeds Q (A ++ B) o) :
    Embeds Q B (o + A.length) := by
  intro i x hx
  have := h (A.length + i) x (by rw [List.getElem?_append_right (by omega)]; simpa using hx)
  rwa [← Nat.add_assoc] at this

lemma embeds_app_left {Q A B : Program} {o : ℕ} (h : Embeds Q (A ++ B) o) : Embeds Q A o := by
  intro i x hx
  exact h i x (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]; exact hx)

lemma run_exec_seg {Q B : Program} {off c n i : ℕ} {ins : Instr} (hE : Embeds Q B (off + c))
    {s : State} {ω : ℕ → Bool} {k : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + n)
    (hn : i + c = n) (hB : B[i]? = some ins) : run Q s ω (k + 1) = run Q (exec ω ins s) ω k :=
  run_exec_at hE hh (by rw [hpc]; omega) hB

lemma cw_exec_seg {Q B : Program} {off c n i : ℕ} {ins : Instr} (hE : Embeds Q B (off + c))
    {s : State} {k : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + n) (hn : i + c = n)
    (hB : B[i]? = some ins) :
    cellsWritten Q s (k + 1) = (wcell ins s).toFinset ∪ cellsWritten Q (exec detTape ins s) k :=
  cw_exec_at hE hh (by rw [hpc]; omega) hB

end DetANN.HPIM.SegStep

-- ===== T32_EvProg =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP

lemma len_fw (off : ℕ) : (fw off).length = 23 := rfl

end DetANN.Supplement.Thm32

-- ===== T32_PreProg =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP

lemma len_preA (q : ℚ) (off : ℕ) : (preA q off).length = 41 := rfl

lemma len_preB0 (q : ℚ) (off : ℕ) : (preB0 q off).length = 51 := rfl

lemma emb_preB {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB0 q off ++ preB1 q off ++ preB2 q off ++ preB3 q off ++ preB4 q off ++ preB5 q off ++ preB6 q off) (off + 64) := by
  have h := embeds_app_right hE
  simpa only [List.length_append, len_preA, len_fw, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_preB1 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB1 q off) (off + 115) := by
  have h := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (emb_preB hE))))))
  simpa only [List.length_append, len_preB0, Nat.add_assoc, Nat.reduceAdd] using h

end DetANN.Supplement.Thm32

-- ===== T32_PreSegB =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma prm_init (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 115) (hh : s.halted = false) :
    (run Q s detTape 2).core.pc = off + 117 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 10 = 0 ∧
      (run Q s detTape 2).core.ptrs 33 = 0 ∧
      (∀ x, x ≠ 10 → x ≠ 33 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma x_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 117) (hh : s.halted = false)
    (hb0 : s.core.ptrs 10 < s.core.ptrs 28) :
    (run Q s detTape 4).core.pc = off + 117 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 10 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 4).core.ptrs 33 = s.core.ptrs 33 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 10 → x ≠ 33 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- `X = 8·N·d`; `p₀ = 0`, `pw = 1`. -/
lemma x_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 117) (hh : s.halted = false)
    (hb0 : s.core.ptrs 28 ≤ s.core.ptrs 10) :
    (run Q s detTape 6).core.pc = off + 126 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 33 = 8 * s.core.ptrs 33 ∧
      (run Q s detTape 6).core.ptrs 34 = 0 ∧
      (run Q s detTape 6).core.ptrs 35 = 1 ∧
      (∀ x, x ≠ 33 → x ≠ 34 → x ≠ 35 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma p_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 126) (hh : s.halted = false)
    (hb0 : s.core.ptrs 35 < s.core.ptrs 33) :
    (run Q s detTape 5).core.pc = off + 126 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 34 = s.core.ptrs 34 + 1 ∧
      (run Q s detTape 5).core.ptrs 35 = 4 * s.core.ptrs 35 ∧
      (∀ x, x ≠ 34 → x ≠ 35 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- `2p₀`, `4p₀`, `q·p₀`, `τ²`; `L = 1`. -/
lemma p_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 126) (hh : s.halted = false)
    (hb0 : s.core.ptrs 33 ≤ s.core.ptrs 35) :
    (run Q s detTape 12).core.pc = off + 142 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 14 = 1 ∧
      (run Q s detTape 12).core.ptrs 36 = 2 * s.core.ptrs 34 ∧
      (run Q s detTape 12).core.ptrs 37 = 2 * s.core.ptrs 34 + 1 ∧
      (run Q s detTape 12).core.ptrs 38 = 4 * s.core.ptrs 34 ∧
      (run Q s detTape 12).core.ptrs 39 = 4 * s.core.ptrs 34 + 1 ∧
      (∀ x, x ≠ 14 → x ≠ 36 → x ≠ 37 → x ≠ 38 → x ≠ 39 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs 0 = (((s.core.ptrs 34 : ℤ)) : ℝ) ∧
      (run Q s detTape 12).core.regs 9 = ((q : ℚ) : ℝ) ∧
      (run Q s detTape 12).core.regs 10 = (((q : ℚ) : ℝ) * (((s.core.ptrs 34 : ℤ)) : ℝ)) ∧
      (run Q s detTape 12).core.regs 11 = (s.core.regs 5 * s.core.regs 5) ∧
      (∀ x, x ≠ 0 → x ≠ 9 → x ≠ 10 → x ≠ 11 → (run Q s detTape 12).core.regs x = s.core.regs x) ∧
      (run Q s detTape 12).core.mem = s.core.mem ∧
      (run Q s detTape 12).integerMemory = s.integerMemory ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      cellsWritten Q s 12 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- Double `L`. -/
lemma l_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 142) (hh : s.halted = false)
    (hb0 : ¬ (s.core.regs 10 - ((((s.core.ptrs 14 : ℤ)) : ℝ) * s.core.regs 11)) ≤ 0) :
    (run Q s detTape 6).core.pc = off + 142 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 14 = 2 * s.core.ptrs 14 ∧
      (∀ x, x ≠ 14 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 0 = (((s.core.ptrs 14 : ℤ)) : ℝ) ∧
      (run Q s detTape 6).core.regs 2 = (s.core.regs 10 - ((((s.core.ptrs 14 : ℤ)) : ℝ) * s.core.regs 11)) ∧
      (∀ x, x ≠ 0 → x ≠ 2 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma l_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 142) (hh : s.halted = false)
    (hb0 : (s.core.regs 10 - ((((s.core.ptrs 14 : ℤ)) : ℝ) * s.core.regs 11)) ≤ 0) :
    (run Q s detTape 4).core.pc = off + 148 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 4).core.regs 0 = (((s.core.ptrs 14 : ℤ)) : ℝ) ∧
      (run Q s detTape 4).core.regs 2 = (s.core.regs 10 - ((((s.core.ptrs 14 : ℤ)) : ℝ) * s.core.regs 11)) ∧
      (∀ x, x ≠ 0 → x ≠ 2 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- The seven arrays; `Fb[0] = 1`. -/
lemma ld_alloc (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 148) (hh : s.halted = false) :
    (run Q s detTape 16).core.pc = off + 164 ∧
      (run Q s detTape 16).halted = false ∧
      (run Q s detTape 16).core.ptrs 10 = 1 ∧
      (run Q s detTape 16).core.ptrs 23 = s.core.ptrs 23 + 3 * s.core.ptrs 39 + 4 * s.core.ptrs 37 ∧
      (run Q s detTape 16).core.ptrs 40 = s.core.ptrs 23 ∧
      (run Q s detTape 16).core.ptrs 41 = s.core.ptrs 23 + s.core.ptrs 39 ∧
      (run Q s detTape 16).core.ptrs 42 = s.core.ptrs 23 + 2 * s.core.ptrs 39 ∧
      (run Q s detTape 16).core.ptrs 43 = s.core.ptrs 23 + 3 * s.core.ptrs 39 ∧
      (run Q s detTape 16).core.ptrs 44 = s.core.ptrs 23 + 3 * s.core.ptrs 39 + s.core.ptrs 37 ∧
      (run Q s detTape 16).core.ptrs 45 = s.core.ptrs 23 + 3 * s.core.ptrs 39 + 2 * s.core.ptrs 37 ∧
      (run Q s detTape 16).core.ptrs 46 = s.core.ptrs 23 + 3 * s.core.ptrs 39 + 3 * s.core.ptrs 37 ∧
      (∀ x, x ≠ 10 → x ≠ 23 → x ≠ 40 → x ≠ 41 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 16).core.regs = s.core.regs ∧
      (run Q s detTape 16).core.mem (s.core.ptrs 23) = s.core.regs 7 ∧
      (∀ z, z ≠ s.core.ptrs 23 → (run Q s detTape 16).core.mem z = s.core.mem z) ∧
      (run Q s detTape 16).integerMemory = s.integerMemory ∧
      (run Q s detTape 16).work = s.work + 16 ∧
      ∀ c ∈ cellsWritten Q s 16, c = (true, s.core.ptrs 23) := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- `Fb[i] = Fb[i-1]·i`. -/
lemma ft_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (v : ℝ) (s : State)
    (hpc : s.core.pc = off + 164) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 10 - 1) = v)
    (hb0 : s.core.ptrs 10 < s.core.ptrs 39) :
    (run Q s detTape 10).core.pc = off + 164 ∧
      (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 10 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 10).core.ptrs 11 = s.core.ptrs 40 + s.core.ptrs 10 ∧
      (∀ x, x ≠ 10 → x ≠ 11 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs 0 = (v * (((s.core.ptrs 10 : ℤ)) : ℝ)) ∧
      (run Q s detTape 10).core.regs 1 = (((s.core.ptrs 10 : ℤ)) : ℝ) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → (run Q s detTape 10).core.regs x = s.core.regs x) ∧
      (run Q s detTape 10).core.mem (s.core.ptrs 40 + s.core.ptrs 10) = (v * (((s.core.ptrs 10 : ℤ)) : ℝ)) ∧
      (∀ z, z ≠ s.core.ptrs 40 + s.core.ptrs 10 → (run Q s detTape 10).core.mem z = s.core.mem z) ∧
      (run Q s detTape 10).integerMemory = s.integerMemory ∧
      (run Q s detTape 10).work = s.work + 10 ∧
      ∀ c ∈ cellsWritten Q s 10, c = (true, s.core.ptrs 40 + s.core.ptrs 10) := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 40 + ptrs 10 - 1 → mem z = v := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- `Sb = -1-d`, `LD = 0`. -/
lemma ft_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 164) (hh : s.halted = false)
    (hb0 : s.core.ptrs 39 ≤ s.core.ptrs 10) :
    (run Q s detTape 5).core.pc = off + 178 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 10 = 0 ∧
      (run Q s detTape 5).core.ptrs 15 = -s.core.ptrs 3 - 1 ∧
      (run Q s detTape 5).core.ptrs 47 = 0 ∧
      (∀ x, x ≠ 10 → x ≠ 15 → x ≠ 47 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma ldl_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 178) (hh : s.halted = false)
    (hb0 : s.core.ptrs 10 < s.core.ptrs 14) :
    (run Q s detTape 4).core.pc = off + 178 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 10 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 4).core.ptrs 47 = s.core.ptrs 47 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 10 → x ≠ 47 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma ldl_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 178) (hh : s.halted = false)
    (hb0 : s.core.ptrs 14 ≤ s.core.ptrs 10) :
    (run Q s detTape 2).core.pc = off + 183 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 48 = 0 ∧
      (∀ x, x ≠ 48 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Sign `k` := `-1`. -/
lemma si_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 183) (hh : s.halted = false)
    (hb0 : s.core.ptrs 48 < s.core.ptrs 47) :
    (run Q s detTape 5).core.pc = off + 183 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 11 = s.core.ptrs 15 - s.core.ptrs 48 ∧
      (run Q s detTape 5).core.ptrs 48 = s.core.ptrs 48 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 48 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 15 - s.core.ptrs 48) = s.core.regs 8 ∧
      (∀ z, z ≠ s.core.ptrs 15 - s.core.ptrs 48 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 15 - s.core.ptrs 48) := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma si_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 183) (hh : s.halted = false)
    (hb0 : s.core.ptrs 47 ≤ s.core.ptrs 48) :
    (run Q s detTape 1).core.pc = off + 188 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB1 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

end DetANN.Supplement.Thm32

-- ===== T32_PreParams =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma momentOrder_eq (N d p0 : ℕ) (h1 : 8 * (N * d) ≤ 4 ^ p0)
    (h2 : ∀ p : ℕ, p < p0 → 4 ^ p < 8 * (N * d)) : momentOrder N d = p0 := by
  unfold momentOrder
  have hX : ((8 * (N * d) : ℕ) : ℝ) = 8 * (N : ℝ) * d := by push_cast; ring
  rcases Nat.eq_zero_or_pos (8 * (N * d)) with h0 | h0
  · have hp : p0 = 0 := by
      by_contra hne
      have := h2 0 (Nat.pos_of_ne_zero hne); omega
    subst hp
    have : (8 : ℝ) * N * d = 0 := by rw [← hX, h0]; simp
    rw [this, Real.logb_zero]; simp
  · have hpos : (0 : ℝ) < 8 * (N : ℝ) * d := by rw [← hX]; exact_mod_cast h0
    apply le_antisymm
    · rw [Nat.ceil_le, Real.logb_le_iff_le_rpow (by norm_num) hpos, Real.rpow_natCast, ← hX]
      exact_mod_cast h1
    · rcases Nat.eq_zero_or_pos p0 with hp | hp
      · rw [hp]; exact Nat.zero_le _
      · have := h2 (p0 - 1) (by omega)
        have hlt : ((p0 - 1 : ℕ) : ℝ) < Real.logb 4 (8 * N * d) := by
          rw [Real.lt_logb_iff_rpow_lt (by norm_num) hpos, Real.rpow_natCast, ← hX]
          exact_mod_cast this
        have := Nat.lt_ceil.2 hlt
        omega

lemma x_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (N d : ℕ) :
    ∀ (kk i : ℕ) (s : State), i + kk = N → s.core.pc = off + 117 → s.halted = false →
      s.core.ptrs 10 = i → s.core.ptrs 28 = N → s.core.ptrs 3 = d →
      s.core.ptrs 33 = ((i * d : ℕ) : ℤ) →
      ∃ t, t ≤ 4 * kk + 6 ∧ (run Q s detTape t).core.pc = off + 126 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 33 = ((8 * (N * d) : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 34 = 0 ∧ (run Q s detTape t).core.ptrs 35 = 1 ∧
        (∀ y, y ≠ 10 → y ≠ 33 → y ≠ 34 → y ≠ 35 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro i s hik hpc hh h10 h28 h3 h33
    have hi : i = N := by omega
    subst hi
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
      x_exit Q off q hE s hpc hh (by rw [h28, h10])
    exact ⟨6, by omega, g1, g2, by rw [g3, h33]; push_cast; ring, g4, g5,
      fun y _ a b c => g6 y a b c, g7, g8, g9, g10⟩
  | succ kk ih =>
    intro i s hik hpc hh h10 h28 h3 h33
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      x_step Q off q hE s hpc hh (by rw [h10, h28]; exact_mod_cast (by omega : i < N))
    set s1 := run Q s detTape 4 with hs1
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (i + 1) s1 (by omega) g1 g2 (by rw [g3, h10]; push_cast; ring)
        (by rw [g5 28 (by decide) (by decide), h28]) (by rw [g5 3 (by decide) (by decide), h3])
        (by rw [g4, h33, h3]; push_cast; ring)
    refine ⟨4 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, q3, q4, q5, fun y a b c e => by rw [q6 y a b c e, g5 y a b], by rw [q7, g6],
      by rw [q8, g7], by rw [q9, g8], by rw [q10, g9]; ring⟩

lemma p_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (X : ℕ) :
    ∀ (kk p : ℕ) (s : State), X ≤ 4 ^ (p + kk) → (∀ p' : ℕ, p' < p → 4 ^ p' < X) →
      s.core.pc = off + 126 → s.halted = false → s.core.ptrs 34 = p →
      s.core.ptrs 35 = ((4 ^ p : ℕ) : ℤ) → s.core.ptrs 33 = X →
      ∃ t p0, t ≤ 5 * kk + 12 ∧ X ≤ 4 ^ p0 ∧ (∀ p' : ℕ, p' < p0 → 4 ^ p' < X) ∧
        (run Q s detTape t).core.pc = off + 142 ∧ (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 34 = p0 ∧ (run Q s detTape t).core.ptrs 14 = 1 ∧
        (run Q s detTape t).core.ptrs 36 = 2 * (p0 : ℤ) ∧
        (run Q s detTape t).core.ptrs 37 = 2 * (p0 : ℤ) + 1 ∧
        (run Q s detTape t).core.ptrs 38 = 4 * (p0 : ℤ) ∧
        (run Q s detTape t).core.ptrs 39 = 4 * (p0 : ℤ) + 1 ∧
        (∀ y, y ≠ 14 → y ≠ 34 → y ≠ 35 → y ≠ 36 → y ≠ 37 → y ≠ 38 → y ≠ 39 →
          (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (run Q s detTape t).core.regs 10 = ((q : ℚ) : ℝ) * (p0 : ℝ) ∧
        (run Q s detTape t).core.regs 11 = s.core.regs 5 * s.core.regs 5 ∧
        (run Q s detTape t).core.regs 9 = ((q : ℚ) : ℝ) ∧
        (∀ y, y ≠ 0 → y ≠ 9 → y ≠ 10 → y ≠ 11 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro p s hX hlt hpc hh h34 h35 h33
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, _⟩ :=
      p_exit Q off q hE s hpc hh (by rw [h33, h35]; exact_mod_cast (by simpa using hX))
    refine ⟨12, p, by omega, by simpa using hX, hlt, g1, g2,
      by rw [g8 34 (by decide) (by decide) (by decide) (by decide) (by decide), h34], g3,
      by rw [g4, h34], by rw [g5, h34], by rw [g6, h34], by rw [g7, h34],
      fun y a b _ c e f g' => g8 y a c e f g', by rw [g11, h34]; push_cast; rfl, g12, g10,
      fun y a b c e => g13 y a b c e, g14, g15, g16⟩
  | succ kk ih =>
    intro p s hX hlt hpc hh h34 h35 h33
    by_cases hc : X ≤ 4 ^ p
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, _⟩ :=
        p_exit Q off q hE s hpc hh (by rw [h33, h35]; exact_mod_cast hc)
      refine ⟨12, p, by omega, hc, hlt, g1, g2,
        by rw [g8 34 (by decide) (by decide) (by decide) (by decide) (by decide), h34], g3,
        by rw [g4, h34], by rw [g5, h34], by rw [g6, h34], by rw [g7, h34],
        fun y a b _ c e f g' => g8 y a c e f g', by rw [g11, h34]; push_cast; rfl, g12, g10,
        fun y a b c e => g13 y a b c e, g14, g15, g16⟩
    · push Not at hc
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
        p_step Q off q hE s hpc hh (by rw [h33, h35]; exact_mod_cast hc)
      set s1 := run Q s detTape 5 with hs1
      obtain ⟨t2, p0, ht2, r1, r2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q9', q12, q13, q14, q15⟩ :=
        ih (p + 1) s1 (by rw [show p + 1 + kk = p + (kk + 1) by ring]; exact hX)
          (by
            intro p' hp'
            rcases Nat.lt_or_ge p' p with h | h
            · exact hlt p' h
            · have : p' = p := by omega
              subst this; exact hc)
          g1 g2 (by rw [g3, h34]; push_cast; ring) (by rw [g4, h35]; push_cast; ring)
          (by rw [g5 33 (by decide) (by decide), h33])
      refine ⟨5 + t2, p0, by omega, r1, r2, ?_⟩
      rw [run_add, ← hs1]
      exact ⟨q1, q2, q3, q4, q5, q6, q7, q8, fun y a b c e f g' h => by
          rw [q9 y a b c e f g' h, g5 y b c], by rw [q10], by rw [q11, g6], q9',
        fun y a b c e => by rw [q12 y a b c e, g6], by rw [q13, g7], by rw [q14, g8],
        by rw [q15, g9]; ring⟩

lemma l_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (c τ2 : ℝ) :
    ∀ (kk m : ℕ) (s : State), c ≤ 2 ^ (m + kk) * τ2 → (∀ m' : ℕ, m' < m → 2 ^ m' * τ2 < c) →
      s.core.pc = off + 142 → s.halted = false → s.core.ptrs 14 = ((2 ^ m : ℕ) : ℤ) →
      s.core.regs 10 = c → s.core.regs 11 = τ2 →
      ∃ t m0, t ≤ 6 * (m0 - m) + 4 ∧ m ≤ m0 ∧ c ≤ 2 ^ m0 * τ2 ∧
        (∀ m' : ℕ, m' < m0 → 2 ^ m' * τ2 < c) ∧
        (run Q s detTape t).core.pc = off + 148 ∧ (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 14 = ((2 ^ m0 : ℕ) : ℤ) ∧
        (∀ y, y ≠ 14 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro m s hc hlt hpc hh h14 h10 h11
    have hb : s.core.regs 10 - (((s.core.ptrs 14 : ℤ)) : ℝ) * s.core.regs 11 ≤ 0 := by
      rw [h10, h11, h14]; push_cast; simpa using hc
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ := l_exit Q off q hE s hpc hh hb
    exact ⟨4, m, by omega, le_rfl, by simpa using hc, hlt, g1, g2, by rw [g3, h14],
      fun y _ => by rw [g3], fun y a b => g6 y a b, g7, g8, g9⟩
  | succ kk ih =>
    intro m s hc hlt hpc hh h14 h10 h11
    by_cases hb : s.core.regs 10 - (((s.core.ptrs 14 : ℤ)) : ℝ) * s.core.regs 11 ≤ 0
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ := l_exit Q off q hE s hpc hh hb
      have hc' : c ≤ 2 ^ m * τ2 := by
        rw [h10, h11, h14] at hb; push_cast at hb; linarith
      exact ⟨4, m, by omega, le_rfl, hc', hlt, g1, g2, by rw [g3, h14],
        fun y _ => by rw [g3], fun y a b => g6 y a b, g7, g8, g9⟩
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ := l_step Q off q hE s hpc hh hb
      set s1 := run Q s detTape 6 with hs1
      have hlt' : 2 ^ m * τ2 < c := by
        rw [h10, h11, h14] at hb; push_cast at hb; linarith
      obtain ⟨t2, m0, ht2, r0, r1, r2, q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
        ih (m + 1) s1 (by rw [show m + 1 + kk = m + (kk + 1) by ring]; exact hc)
          (by
            intro m' hm'
            rcases Nat.lt_or_ge m' m with h | h
            · exact hlt m' h
            · have : m' = m := by omega
              subst this; exact hlt')
          g1 g2 (by rw [g3, h14]; push_cast; ring) (by rw [g7 10 (by decide) (by decide), h10])
          (by rw [g7 11 (by decide) (by decide), h11])
      refine ⟨6 + t2, m0, by omega, by omega, r1, r2, ?_⟩
      rw [run_add, ← hs1]
      exact ⟨q1, q2, q3, fun y a => by rw [q4 y a, g4 y a], fun y a b => by rw [q5 y a b, g7 y a b],
        by rw [q6, g8], by rw [q7, g9], by rw [q8, g10]; ring⟩

lemma ft_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (K1 : ℕ) (Fb : ℤ)
    (m0 : ℤ → ℝ) :
    ∀ (kk i : ℕ) (s : State), i + kk = K1 → 1 ≤ i → s.core.pc = off + 164 → s.halted = false →
      s.core.ptrs 10 = i → s.core.ptrs 39 = K1 → s.core.ptrs 40 = Fb →
      (∀ i' : ℕ, i' < i → s.core.mem (Fb + i') = (i'.factorial : ℝ)) →
      (∀ z, (z < Fb ∨ Fb + i ≤ z) → s.core.mem z = m0 z) →
      ∃ t, t ≤ 10 * kk + 5 ∧ (run Q s detTape t).core.pc = off + 178 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 10 = 0 ∧
        (run Q s detTape t).core.ptrs 15 = -s.core.ptrs 3 - 1 ∧
        (run Q s detTape t).core.ptrs 47 = 0 ∧
        (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 15 → y ≠ 47 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (∀ i' : ℕ, i' < K1 → (run Q s detTape t).core.mem (Fb + i') = (i'.factorial : ℝ)) ∧
        (∀ z, (z < Fb ∨ Fb + K1 ≤ z) → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro i s hik hi1 hpc hh h10 h39 h40 hf hout
    have hi : i = K1 := by omega
    subst hi
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ := ft_exit Q off q hE s hpc hh (by rw [h39, h10])
    exact ⟨5, by omega, g1, g2, g3, g4, g5, fun y a _ b c => g6 y a b c, fun y _ _ => by rw [g7],
      fun i' h => by rw [g8]; exact hf i' h, fun z hz => by rw [g8]; exact hout z hz, g9, g10⟩
  | succ kk ih =>
    intro i s hik hi1 hpc hh h10 h39 h40 hf hout
    have hi : i < K1 := by omega
    have e0 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 10 - 1) = ((i - 1).factorial : ℝ) := by
      rw [h40, h10, show Fb + (i : ℤ) - 1 = Fb + ((i - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hi1]; ring]
      exact hf (i - 1) (by omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
      ft_step Q off q hE _ s hpc hh e0 (by rw [h10, h39]; exact_mod_cast hi)
    set s1 := run Q s detTape 10 with hs1
    rw [h40, h10] at g9 g10
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
      ih (i + 1) s1 (by omega) (by omega) g1 g2 (by rw [g3, h10]; push_cast; ring)
        (by rw [g5 39 (by decide) (by decide), h39]) (by rw [g5 40 (by decide) (by decide), h40])
        (by
          intro i' hi'
          rcases Nat.lt_or_ge i' i with h | h
          · rw [g10 _ (by intro e; have := add_left_cancel e; omega)]; exact hf i' h
          · have : i' = i := by omega
            subst this
            rw [g9]
            obtain ⟨j, rfl⟩ : ∃ j, i' = j + 1 := ⟨i' - 1, by omega⟩
            simp [Nat.factorial_succ]; push_cast; ring)
        (by
          intro z hz
          rw [g10 z (by intro e; subst e; rcases hz with hz | hz <;> push_cast at hz <;> omega)]
          exact hout z (by rcases hz with hz | hz
                           · left; exact hz
                           · right; push_cast at hz; omega))
    refine ⟨10 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, q3, by rw [q4, g5 3 (by decide) (by decide)], q5,
      fun y a b c e => by rw [q6 y a b c e, g5 y a b], fun y a b => by rw [q7 y a b, g8 y a b], q8, q9,
      by rw [q10, g11], by rw [q11, g12]; ring⟩

lemma ldl_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (L d : ℕ) :
    ∀ (kk i : ℕ) (s : State), i + kk = L → s.core.pc = off + 178 → s.halted = false →
      s.core.ptrs 10 = i → s.core.ptrs 14 = L → s.core.ptrs 3 = d →
      s.core.ptrs 47 = ((i * d : ℕ) : ℤ) →
      ∃ t, t ≤ 4 * kk + 2 ∧ (run Q s detTape t).core.pc = off + 183 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 47 = ((L * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 48 = 0 ∧
        (∀ y, y ≠ 10 → y ≠ 47 → y ≠ 48 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro i s hik hpc hh h10 h14 h3 h47
    have hi : i = L := by omega
    subst hi
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ := ldl_exit Q off q hE s hpc hh (by rw [h14, h10])
    exact ⟨2, by omega, g1, g2, by rw [g4 47 (by decide), h47], g3, fun y _ _ c => g4 y c, g5, g6,
      g7, g8⟩
  | succ kk ih =>
    intro i s hik hpc hh h10 h14 h3 h47
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      ldl_step Q off q hE s hpc hh (by rw [h10, h14]; exact_mod_cast (by omega : i < L))
    set s1 := run Q s detTape 4 with hs1
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (i + 1) s1 (by omega) g1 g2 (by rw [g3, h10]; push_cast; ring)
        (by rw [g5 14 (by decide) (by decide), h14]) (by rw [g5 3 (by decide) (by decide), h3])
        (by rw [g4, h47, h3]; push_cast; ring)
    refine ⟨4 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, q3, q4, fun y a b c => by rw [q5 y a b c, g5 y a b], by rw [q6, g6], by rw [q7, g7],
      by rw [q8, g8], by rw [q9, g9]; ring⟩

lemma si_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (LD : ℕ) (Sb : ℤ)
    (m0 : ℤ → ℝ) :
    ∀ (kk k : ℕ) (s : State), k + kk = LD → s.core.pc = off + 183 → s.halted = false →
      s.core.ptrs 48 = k → s.core.ptrs 47 = LD → s.core.ptrs 15 = Sb → s.core.regs 8 = -1 →
      (∀ k' : ℕ, k' < k → s.core.mem (Sb - k') = -1) →
      (∀ z, (Sb < z ∨ z ≤ Sb - k) → s.core.mem z = m0 z) →
      ∃ t, t ≤ 5 * kk + 1 ∧ (run Q s detTape t).core.pc = off + 188 ∧
        (run Q s detTape t).halted = false ∧
        (∀ y, y ≠ 11 → y ≠ 48 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧
        (∀ k' : ℕ, k' < LD → (run Q s detTape t).core.mem (Sb - k') = -1) ∧
        (∀ z, (Sb < z ∨ z ≤ Sb - LD) → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro k s hkk hpc hh h48 h47 h15 h8 hs hout
    have hk : k = LD := by omega
    subst hk
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ := si_exit Q off q hE s hpc hh (by rw [h47, h48])
    exact ⟨1, by omega, g1, g2, fun y _ _ => by rw [g3], g4, fun k' h => by rw [g5]; exact hs k' h,
      fun z hz => by rw [g5]; exact hout z hz, g6, g7⟩
  | succ kk ih =>
    intro k s hkk hpc hh h48 h47 h15 h8 hs hout
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
      si_step Q off q hE s hpc hh (by rw [h48, h47]; exact_mod_cast (by omega : k < LD))
    set s1 := run Q s detTape 5 with hs1
    rw [h15, h48, h8] at g7
    rw [h15, h48] at g8
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
      ih (k + 1) s1 (by omega) g1 g2 (by rw [g4, h48]; push_cast; ring)
        (by rw [g5 47 (by decide) (by decide), h47]) (by rw [g5 15 (by decide) (by decide), h15])
        (by rw [g6, h8])
        (by
          intro k' hk'
          rcases Nat.lt_or_ge k' k with h | h
          · have hne : Sb - (k' : ℤ) ≠ Sb - (k : ℤ) := by
              intro e
              have : (k' : ℤ) = k := by linarith
              omega
            rw [g8 _ hne]; exact hs k' h
          · have : k' = k := by omega
            subst this; exact g7)
        (by
          intro z hz
          rw [g8 z (by intro e; subst e; rcases hz with hz | hz <;> push_cast at hz <;> omega)]
          exact hout z (by rcases hz with hz | hz
                           · left; exact hz
                           · right; push_cast at hz; omega))
    refine ⟨5 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, fun y a b => by rw [q3 y a b, g5 y a b], by rw [q4, g6], q5, q6, by rw [q7, g9],
      by rw [q8, g10]; ring⟩

/-- **Parameters and tables.** From `off + 115` with `N` in pointer `28`, `d ≥ 1` in pointer `3`,
`top ≥ 0` in pointer `23`, `τ > 0` in real `5` and the constants `1`, `-1` in reals `7`, `8`, `pre`
reaches `off + 188` with `p₀ = momentOrder N d`, `L = 2^m` the least power of two with
`L·τ² ≥ q·p₀`, the arrays allocated from `top`, `Fb[i] = i!` for `i ≤ 4p₀`, and the signs
`-1` at `-d-1-k` for `k < L·d`. -/
lemma pre_params (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (N d : ℕ)
    (top : ℤ) (τ : ℝ) (htop : 0 ≤ top) (hτ : 0 < τ) (s : State) (hpc : s.core.pc = off + 115)
    (hh : s.halted = false) (h28 : s.core.ptrs 28 = N) (h3 : s.core.ptrs 3 = d)
    (h23 : s.core.ptrs 23 = top) (h5 : s.core.regs 5 = τ) (h7 : s.core.regs 7 = 1)
    (h8 : s.core.regs 8 = -1) :
    ∃ t m, (run Q s detTape t).core.pc = off + 188 ∧ (run Q s detTape t).halted = false ∧
      ((q : ℚ) : ℝ) * (momentOrder N d : ℝ) ≤ 2 ^ m * (τ * τ) ∧
      (∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < ((q : ℚ) : ℝ) * (momentOrder N d : ℝ)) ∧
      t ≤ 48 + 4 * N + 40 * (N * d) + 6 * m + 40 * momentOrder N d + 4 * 2 ^ m + 5 * (2 ^ m * d) ∧
      (run Q s detTape t).core.ptrs 14 = ((2 ^ m : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 34 = momentOrder N d ∧
      (run Q s detTape t).core.ptrs 36 = 2 * (momentOrder N d : ℤ) ∧
      (run Q s detTape t).core.ptrs 37 = 2 * (momentOrder N d : ℤ) + 1 ∧
      (run Q s detTape t).core.ptrs 38 = 4 * (momentOrder N d : ℤ) ∧
      (run Q s detTape t).core.ptrs 39 = 4 * (momentOrder N d : ℤ) + 1 ∧
      (run Q s detTape t).core.ptrs 40 = top ∧
      (run Q s detTape t).core.ptrs 41 = top + (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 42 = top + 2 * (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 43 = top + 3 * (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 44 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 45 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 2 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 46 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 3 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 23 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 4 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 15 = -(d : ℤ) - 1 ∧
      (run Q s detTape t).core.ptrs 47 = ((2 ^ m * d : ℕ) : ℤ) ∧
      (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 14 → y ≠ 15 → y ≠ 23 → y < 33 ∨ 48 < y →
        (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (run Q s detTape t).core.regs 9 = ((q : ℚ) : ℝ) ∧
      (run Q s detTape t).core.regs 10 = ((q : ℚ) : ℝ) * (momentOrder N d : ℝ) ∧
      (run Q s detTape t).core.regs 11 = τ * τ ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → y ≠ 9 → y ≠ 10 → y ≠ 11 →
        (run Q s detTape t).core.regs y = s.core.regs y) ∧
      (∀ i : ℕ, i < 4 * momentOrder N d + 1 →
        (run Q s detTape t).core.mem (top + i) = (i.factorial : ℝ)) ∧
      (∀ k : ℕ, k < 2 ^ m * d → (run Q s detTape t).core.mem (-(d : ℤ) - 1 - k) = -1) ∧
      (∀ z, (z < top ∨ top + (4 * momentOrder N d + 1 : ℕ) ≤ z) →
        (-(d : ℤ) - 1 < z ∨ z ≤ -(d : ℤ) - 1 - ((2 ^ m * d : ℕ) : ℤ)) →
        (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by
  -- init and X
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ := prm_init Q off q hE s hpc hh
  set s1 := run Q s detTape 2 with hs1
  obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ :=
    x_loop Q off q hE N d N 0 s1 (by omega) g1 g2 g3 (by rw [g5 28 (by decide) (by decide), h28])
      (by rw [g5 3 (by decide) (by decide), h3]) (by rw [g4]; simp)
  set s2 := run Q s1 detTape t2 with hs2
  -- p0
  have hXb : 8 * (N * d) < 4 ^ (8 * (N * d)) := Nat.lt_pow_self (by norm_num)
  obtain ⟨t3, p0, ht3, hp1, hp2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q9r, q12, q13, q14, q15⟩ :=
    p_loop Q off q hE (8 * (N * d)) (8 * (N * d)) 0 s2 (by simpa using hXb.le)
      (fun p' h => absurd h (Nat.not_lt_zero _)) p1 p2 p4 (by rw [p5]; simp) p3
  set s3 := run Q s2 detTape t3 with hs3
  have hmo : momentOrder N d = p0 := momentOrder_eq N d p0 hp1 hp2
  have hr5 : s2.core.regs 5 = τ := by rw [p7, g6, h5]
  rw [hr5] at q11
  -- L
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ((q : ℚ) : ℝ) * (p0 : ℝ) ≤ 2 ^ M * (τ * τ) := by
    have hτ2 : 0 < τ * τ := by positivity
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (((q : ℚ) : ℝ) * (p0 : ℝ) / (τ * τ))
      (by norm_num : (1 : ℝ) < 2)
    exact ⟨M, by rw [div_lt_iff₀ hτ2] at hM; linarith⟩
  obtain ⟨t4, m, ht4, _, hm1, hm2, r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
    l_loop Q off q hE (((q : ℚ) : ℝ) * (p0 : ℝ)) (τ * τ) M 0 s3 (by simpa using hM)
      (fun m' h => absurd h (Nat.not_lt_zero _)) q1 q2 (by rw [q4]; simp) q10 q11
  set s4 := run Q s3 detTape t4 with hs4
  have f4 : ∀ y, y ≠ 10 → y ≠ 14 → y ≠ 33 → y ≠ 34 → y ≠ 35 → y ≠ 36 → y ≠ 37 → y ≠ 38 → y ≠ 39 →
      s4.core.ptrs y = s.core.ptrs y :=
    fun y a b c e f g' h i j => by
      rw [r4 y b, q9 y b e f g' h i j, p6 y a c e f, g5 y a c]
  have reg4 : ∀ y, y ≠ 0 → y ≠ 2 → y ≠ 9 → y ≠ 10 → y ≠ 11 → s4.core.regs y = s.core.regs y :=
    fun y a b c e f => by rw [r5 y a b, q12 y a c e f, p7, g6]
  have mem4 : s4.core.mem = s.core.mem := by rw [r6, q13, p8, g7]
  -- allocation
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15, u16, u17, _⟩ :=
    ld_alloc Q off q hE s4 r1 r2
  set s5 := run Q s4 detTape 16 with hs5
  have e23 : s4.core.ptrs 23 = top := by
    rw [f4 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h23]
  have e37 : s4.core.ptrs 37 = 2 * (p0 : ℤ) + 1 := by rw [r4 37 (by decide), q6]
  have e39 : s4.core.ptrs 39 = 4 * (p0 : ℤ) + 1 := by rw [r4 39 (by decide), q8]
  have r7' : s4.core.regs 7 = 1 := by
    rw [reg4 7 (by decide) (by decide) (by decide) (by decide) (by decide), h7]
  rw [e23, r7'] at u14
  rw [e23] at u15
  have f5 : ∀ y, y ≠ 10 → y ≠ 23 → y ≠ 40 → y ≠ 41 → y ≠ 42 → y ≠ 43 → y ≠ 44 → y ≠ 45 → y ≠ 46 →
      s5.core.ptrs y = s4.core.ptrs y := u12
  -- factorials
  obtain ⟨T6, hT6, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ :=
    ft_loop Q off q hE (4 * p0 + 1) top s5.core.mem (4 * p0) 1 s5 (by omega) le_rfl u1 u2 u3
      (by rw [f5 39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), e39]; push_cast; ring)
      (by rw [u5, e23])
      (fun i' h => by
        have : i' = 0 := by omega
        subst this; simpa using u14)
      (fun z _ => rfl)
  set s6 := run Q s5 detTape T6 with hs6
  have e3 : s5.core.ptrs 3 = d := by
    rw [f5 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), f4 3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), h3]
  have e14 : s5.core.ptrs 14 = ((2 ^ m : ℕ) : ℤ) := by
    rw [f5 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), r3]
  rw [e3] at v4
  -- LD = L·d
  obtain ⟨t7, ht7, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ :=
    ldl_loop Q off q hE (2 ^ m) d (2 ^ m) 0 s6 (by omega) v1 v2 v3
      (by rw [v6 14 (by decide) (by decide) (by decide) (by decide), e14])
      (by rw [v6 3 (by decide) (by decide) (by decide) (by decide), e3]) (by rw [v5]; simp)
  set s7 := run Q s6 detTape t7 with hs7
  have r8' : s7.core.regs 8 = -1 := by
    rw [w6, v7 8 (by decide) (by decide), u13,
      reg4 8 (by decide) (by decide) (by decide) (by decide) (by decide), h8]
  -- signs
  obtain ⟨T8, hT8, x1, x2, x3, x4, x5, x6, x7, x8⟩ :=
    si_loop Q off q hE (2 ^ m * d) (-(d : ℤ) - 1) s7.core.mem (2 ^ m * d) 0 s7 (by omega) w1 w2 w4 w3
      (by rw [w5 15 (by decide) (by decide) (by decide), v4]) r8'
      (fun k' h => absurd h (Nat.not_lt_zero _)) (fun z _ => rfl)
  set s8 := run Q s7 detTape T8 with hs8
  refine ⟨2 + t2 + t3 + t4 + 16 + T6 + t7 + T8, m, ?_⟩
  have e8 : run Q s detTape (2 + t2 + t3 + t4 + 16 + T6 + t7 + T8) = s8 := by
    rw [run_add, run_add, run_add, run_add, run_add, run_add, run_add, ← hs1, ← hs2, ← hs3, ← hs4,
      ← hs5, ← hs6, ← hs7, ← hs8]
  rw [e8, hmo]
  have f58 : ∀ y, y ≠ 10 → y ≠ 11 → y ≠ 15 → y ≠ 47 → y ≠ 48 → s8.core.ptrs y = s5.core.ptrs y :=
    fun y a b c e f => by rw [x3 y b f, w5 y a e f, v6 y a b c e]
  have reg8 : s8.core.regs = s7.core.regs := x4
  have reg85 : ∀ y, y ≠ 0 → y ≠ 1 → s8.core.regs y = s5.core.regs y :=
    fun y a b => by rw [x4, w6, v7 y a b]
  have hp0X : p0 ≤ 8 * (N * d) := by
    by_contra h; push Not at h
    have := hp2 (8 * (N * d)) h; omega
  have hm2' : m ≤ 2 ^ m := (Nat.lt_two_pow_self).le
  have pf : ∀ y, y = 36 ∨ y = 37 ∨ y = 38 ∨ y = 39 ∨ y = 34 ∨ y = 14 → s8.core.ptrs y = s4.core.ptrs y := by
    intro y hy
    rw [f58 y (by omega) (by omega) (by omega) (by omega) (by omega),
      f5 y (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
  refine ⟨x1, x2, hm1, hm2, ?_, by rw [pf 14 (by decide), r3], by rw [pf 34 (by decide), r4 34 (by decide), q3],
    by rw [pf 36 (by decide), r4 36 (by decide), q5], by rw [pf 37 (by decide), e37],
    by rw [pf 38 (by decide), r4 38 (by decide), q7], by rw [pf 39 (by decide), e39],
    by rw [f58 40 (by decide) (by decide) (by decide) (by decide) (by decide), u5, e23],
    by rw [f58 41 (by decide) (by decide) (by decide) (by decide) (by decide), u6, e23, e39],
    by rw [f58 42 (by decide) (by decide) (by decide) (by decide) (by decide), u7, e23, e39],
    by rw [f58 43 (by decide) (by decide) (by decide) (by decide) (by decide), u8, e23, e39],
    by rw [f58 44 (by decide) (by decide) (by decide) (by decide) (by decide), u9, e23, e39, e37],
    by rw [f58 45 (by decide) (by decide) (by decide) (by decide) (by decide), u10, e23, e39, e37],
    by rw [f58 46 (by decide) (by decide) (by decide) (by decide) (by decide), u11, e23, e39, e37],
    by rw [f58 23 (by decide) (by decide) (by decide) (by decide) (by decide), u4, e23, e39, e37],
    by rw [x3 15 (by decide) (by decide), w5 15 (by decide) (by decide) (by decide), v4],
    by rw [x3 47 (by decide) (by decide), w3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 10 * (4 * p0) = 40 * p0 := by ring
    omega
  · intro y a b c e f g'
    have h1 : y ≠ 33 := by rcases g' with h | h <;> omega
    have h2 : y ≠ 34 := by rcases g' with h | h <;> omega
    have h3' : y ≠ 35 := by rcases g' with h | h <;> omega
    have h4 : y ≠ 36 := by rcases g' with h | h <;> omega
    have h5' : y ≠ 37 := by rcases g' with h | h <;> omega
    have h6 : y ≠ 38 := by rcases g' with h | h <;> omega
    have h7' : y ≠ 39 := by rcases g' with h | h <;> omega
    have h8' : y ≠ 40 ∧ y ≠ 41 ∧ y ≠ 42 ∧ y ≠ 43 ∧ y ≠ 44 ∧ y ≠ 45 ∧ y ≠ 46 ∧ y ≠ 47 ∧ y ≠ 48 := by
      rcases g' with h | h <;> omega
    obtain ⟨i40, i41, i42, i43, i44, i45, i46, i47, i48⟩ := h8'
    rw [f58 y a b e i47 i48, f5 y a f i40 i41 i42 i43 i44 i45 i46, f4 y a c h1 h2 h3' h4 h5' h6 h7']
  · rw [reg85 9 (by decide) (by decide), u13, r5 9 (by decide) (by decide), q9r]
  · rw [reg85 10 (by decide) (by decide), u13, r5 10 (by decide) (by decide), q10]
  · rw [reg85 11 (by decide) (by decide), u13, r5 11 (by decide) (by decide), q11]
  · intro y a b c e f g'
    rw [reg85 y a b, u13, reg4 y a c e f g']
  · intro i hi
    have hd0 : (0 : ℤ) ≤ (d : ℤ) := by positivity
    have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
    rw [x6 _ (Or.inl (by omega)), w7]
    exact v8 i hi
  · intro k hk; exact x5 k hk
  · intro z hz1 hz2
    rw [x6 z hz2, w7, v9 z hz1, u15 z (by
      rcases hz1 with h | h
      · omega
      · have : (0 : ℤ) < ((4 * p0 + 1 : ℕ) : ℤ) := by positivity
        omega), mem4]
  · rw [x7, w8, v10, u16, r7, q14, p9, g8]
  · rw [x8, w9, v11, u17, r8, q15, p10, g9]; ring

end DetANN.Supplement.Thm32

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

theorem _root_.solution :
    ∀ (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (N d : ℕ)
    (top : ℤ) (τ : ℝ) (htop : 0 ≤ top) (hτ : 0 < τ) (s : State) (hpc : s.core.pc = off + 115)
    (hh : s.halted = false) (h28 : s.core.ptrs 28 = N) (h3 : s.core.ptrs 3 = d)
    (h23 : s.core.ptrs 23 = top) (h5 : s.core.regs 5 = τ) (h7 : s.core.regs 7 = 1)
    (h8 : s.core.regs 8 = -1),
    ∃ t m, (run Q s detTape t).core.pc = off + 188 ∧ (run Q s detTape t).halted = false ∧
      ((q : ℚ) : ℝ) * (momentOrder N d : ℝ) ≤ 2 ^ m * (τ * τ) ∧
      (∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < ((q : ℚ) : ℝ) * (momentOrder N d : ℝ)) ∧
      t ≤ 48 + 4 * N + 40 * (N * d) + 6 * m + 40 * momentOrder N d + 4 * 2 ^ m + 5 * (2 ^ m * d) ∧
      (run Q s detTape t).core.ptrs 14 = ((2 ^ m : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 34 = momentOrder N d ∧
      (run Q s detTape t).core.ptrs 36 = 2 * (momentOrder N d : ℤ) ∧
      (run Q s detTape t).core.ptrs 37 = 2 * (momentOrder N d : ℤ) + 1 ∧
      (run Q s detTape t).core.ptrs 38 = 4 * (momentOrder N d : ℤ) ∧
      (run Q s detTape t).core.ptrs 39 = 4 * (momentOrder N d : ℤ) + 1 ∧
      (run Q s detTape t).core.ptrs 40 = top ∧
      (run Q s detTape t).core.ptrs 41 = top + (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 42 = top + 2 * (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 43 = top + 3 * (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 44 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 45 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 2 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 46 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 3 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 23 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 4 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 15 = -(d : ℤ) - 1 ∧
      (run Q s detTape t).core.ptrs 47 = ((2 ^ m * d : ℕ) : ℤ) ∧
      (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 14 → y ≠ 15 → y ≠ 23 → y < 33 ∨ 48 < y →
        (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (run Q s detTape t).core.regs 9 = ((q : ℚ) : ℝ) ∧
      (run Q s detTape t).core.regs 10 = ((q : ℚ) : ℝ) * (momentOrder N d : ℝ) ∧
      (run Q s detTape t).core.regs 11 = τ * τ ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → y ≠ 9 → y ≠ 10 → y ≠ 11 →
        (run Q s detTape t).core.regs y = s.core.regs y) ∧
      (∀ i : ℕ, i < 4 * momentOrder N d + 1 →
        (run Q s detTape t).core.mem (top + i) = (i.factorial : ℝ)) ∧
      (∀ k : ℕ, k < 2 ^ m * d → (run Q s detTape t).core.mem (-(d : ℤ) - 1 - k) = -1) ∧
      (∀ z, (z < top ∨ top + (4 * momentOrder N d + 1 : ℕ) ≤ z) →
        (-(d : ℤ) - 1 < z ∨ z ≤ -(d : ℤ) - 1 - ((2 ^ m * d : ℕ) : ℤ)) →
        (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t :=
  DetANN.Supplement.Thm32.pre_params

end DetANN.Supplement.Thm32

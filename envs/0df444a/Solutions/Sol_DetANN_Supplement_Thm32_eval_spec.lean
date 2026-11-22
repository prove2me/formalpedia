-- Prove2me | solution 1 for DetANN.Supplement.Thm32.eval_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-21T08:10:41.226465+00:00
-- url     : https://prove2.me/submissions/5f2d5f18-3d54-4f86-a55c-abc9bd8080c4

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
import Definitions.Def_DetANN_SignChoice
import Definitions.Def_DetANN_Supplement_Greedy
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_Supplement_PreDedup

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

lemma len_preB1 (q : ℚ) (off : ℕ) : (preB1 q off).length = 73 := rfl

lemma len_preB2 (q : ℚ) (off : ℕ) : (preB2 q off).length = 53 := rfl

lemma len_preB3 (q : ℚ) (off : ℕ) : (preB3 q off).length = 41 := rfl

lemma len_preB4 (q : ℚ) (off : ℕ) : (preB4 q off).length = 48 := rfl

lemma len_preB5 (q : ℚ) (off : ℕ) : (preB5 q off).length = 67 := rfl

lemma emb_preB {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB0 q off ++ preB1 q off ++ preB2 q off ++ preB3 q off ++ preB4 q off ++ preB5 q off ++ preB6 q off) (off + 64) := by
  have h := embeds_app_right hE
  simpa only [List.length_append, len_preA, len_fw, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_preB2 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB2 q off) (off + 188) := by
  have h := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (emb_preB hE)))))
  simpa only [List.length_append, len_preB0, len_preB1, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_preB3 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB3 q off) (off + 241) := by
  have h := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (emb_preB hE))))
  simpa only [List.length_append, len_preB0, len_preB1, len_preB2, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_preB4 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB4 q off) (off + 282) := by
  have h := embeds_app_right (embeds_app_left (embeds_app_left (emb_preB hE)))
  simpa only [List.length_append, len_preB0, len_preB1, len_preB2, len_preB3, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_preB5 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB5 q off) (off + 330) := by
  have h := embeds_app_right (embeds_app_left (emb_preB hE))
  simpa only [List.length_append, len_preB0, len_preB1, len_preB2, len_preB3, len_preB4, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_preB6 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB6 q off) (off + 397) := by
  have h := embeds_app_right (emb_preB hE)
  simpa only [List.length_append, len_preB0, len_preB1, len_preB2, len_preB3, len_preB4, len_preB5, Nat.add_assoc, Nat.reduceAdd] using h

end DetANN.Supplement.Thm32

-- ===== T32_PreSegD =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- `tot = 0`; first table entry. -/
lemma ev_init (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 206) (hh : s.halted = false) :
    (run Q s detTape 2).core.pc = off + 208 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 51 = s.core.ptrs 26 ∧
      (∀ x, x ≠ 51 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs 13 = (0 : ℝ) ∧
      (∀ x, x ≠ 13 → (run Q s detTape 2).core.regs x = s.core.regs x) ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- All entries done. -/
lemma ev_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 208) (hh : s.halted = false)
    (hb0 : s.core.ptrs 27 ≤ s.core.ptrs 51) :
    (run Q s detTape 1).core.pc = off + 405 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Return to `R0`. -/
lemma eret0 (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 405) (hh : s.halted = false)
    (hb0 : s.core.ptrs 50 ≤ s.core.ptrs 0) :
    (run Q s detTape 1).core.pc = off + 194 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB6 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Return to `R1`. -/
lemma eret1 (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 405) (hh : s.halted = false)
    (hb0 : s.core.ptrs 0 < s.core.ptrs 50) :
    (run Q s detTape 2).core.pc = off + 198 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB6 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Start `‖v‖²`. -/
lemma ev_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 208) (hh : s.halted = false)
    (hb0 : s.core.ptrs 51 < s.core.ptrs 27) :
    (run Q s detTape 3).core.pc = off + 211 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 31 = 0 ∧
      (∀ x, x ≠ 31 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs 14 = (0 : ℝ) ∧
      (∀ x, x ≠ 14 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma n2_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (x : ℝ) (s : State)
    (hpc : s.core.pc = off + 211) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 51 + s.core.ptrs 31) = x)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3) :
    (run Q s detTape 7).core.pc = off + 211 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 11 = s.core.ptrs 51 + s.core.ptrs 31 ∧
      (run Q s detTape 7).core.ptrs 31 = s.core.ptrs 31 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 31 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 0 = (x * x) ∧
      (run Q s detTape 7).core.regs 14 = (s.core.regs 14 + (x * x)) ∧
      (∀ x, x ≠ 0 → x ≠ 14 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 51 + ptrs 31 → mem z = x := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- `-‖v‖²`; start its powers. -/
lemma n2_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 211) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 31) :
    (run Q s detTape 4).core.pc = off + 221 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 5 = 0 ∧
      (∀ x, x ≠ 5 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs 0 = (1 : ℝ) ∧
      (run Q s detTape 4).core.regs 15 = (s.core.regs 6 - s.core.regs 14) ∧
      (∀ x, x ≠ 0 → x ≠ 15 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma pn_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 221) (hh : s.halted = false)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 37) :
    (run Q s detTape 6).core.pc = off + 221 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 6).core.ptrs 11 = s.core.ptrs 43 + s.core.ptrs 5 ∧
      (∀ x, x ≠ 5 → x ≠ 11 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 0 = (s.core.regs 0 * s.core.regs 15) ∧
      (∀ x, x ≠ 0 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem (s.core.ptrs 43 + s.core.ptrs 5) = s.core.regs 0 ∧
      (∀ z, z ≠ s.core.ptrs 43 + s.core.ptrs 5 → (run Q s detTape 6).core.mem z = s.core.mem z) ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      ∀ c ∈ cellsWritten Q s 6, c = (true, s.core.ptrs 43 + s.core.ptrs 5) := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- `Lτ‖v‖²`; start its power. -/
lemma pn_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 221) (hh : s.halted = false)
    (hb0 : s.core.ptrs 37 ≤ s.core.ptrs 5) :
    (run Q s detTape 6).core.pc = off + 232 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 5 = 0 ∧
      (∀ x, x ≠ 5 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 0 = (1 : ℝ) ∧
      (run Q s detTape 6).core.regs 16 = (((s.core.ptrs 14 : ℤ)) : ℝ) ∧
      (run Q s detTape 6).core.regs 17 = (((((s.core.ptrs 14 : ℤ)) : ℝ) * s.core.regs 5) * s.core.regs 14) ∧
      (∀ x, x ≠ 0 → x ≠ 16 → x ≠ 17 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma bp_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 232) (hh : s.halted = false)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 36) :
    (run Q s detTape 4).core.pc = off + 232 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (∀ x, x ≠ 5 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs 0 = (s.core.regs 0 * s.core.regs 17) ∧
      (∀ x, x ≠ 0 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- The prefactor `(2p₀)!/(Lτ‖v‖²)^{2p₀}`; `j = 0`. -/
lemma bp_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (fv : ℝ) (s : State)
    (hpc : s.core.pc = off + 232) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 36) = fv)
    (hb0 : s.core.ptrs 36 ≤ s.core.ptrs 5) :
    (run Q s detTape 6).core.pc = off + 241 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 11 = s.core.ptrs 40 + s.core.ptrs 36 ∧
      (run Q s detTape 6).core.ptrs 20 = 0 ∧
      (∀ x, x ≠ 11 → x ≠ 20 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 1 = fv ∧
      (run Q s detTape 6).core.regs 18 = ((s.core.regs 7 / s.core.regs 0) * fv) ∧
      (∀ x, x ≠ 1 → x ≠ 18 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 40 + ptrs 36 → mem z = fv := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma ej_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 241) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 20) :
    (run Q s detTape 1).core.pc = off + 403 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Next table entry. -/
lemma evn (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 403) (hh : s.halted = false) :
    (run Q s detTape 2).core.pc = off + 208 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 51 = s.core.ptrs 51 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 51 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB6 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma ej_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 241) (hh : s.halted = false)
    (hb0 : s.core.ptrs 20 < s.core.ptrs 3) :
    (run Q s detTape 2).core.pc = off + 243 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 5 = 0 ∧
      (∀ x, x ≠ 5 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma g0_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 243) (hh : s.halted = false)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 37) :
    (run Q s detTape 5).core.pc = off + 243 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 5).core.ptrs 11 = s.core.ptrs 44 + s.core.ptrs 5 ∧
      (∀ x, x ≠ 5 → x ≠ 11 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 44 + s.core.ptrs 5) = s.core.regs 6 ∧
      (∀ z, z ≠ s.core.ptrs 44 + s.core.ptrs 5 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 44 + s.core.ptrs 5) := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- `G = 1`; `ℓ = 0`. -/
lemma g0_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 243) (hh : s.halted = false)
    (hb0 : s.core.ptrs 37 ≤ s.core.ptrs 5) :
    (run Q s detTape 4).core.pc = off + 251 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 16 = 0 ∧
      (run Q s detTape 4).core.ptrs 17 = 0 ∧
      (∀ x, x ≠ 16 → x ≠ 17 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem (s.core.ptrs 44) = s.core.regs 7 ∧
      (∀ z, z ≠ s.core.ptrs 44 → (run Q s detTape 4).core.mem z = s.core.mem z) ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      ∀ c ∈ cellsWritten Q s 4, c = (true, s.core.ptrs 44) := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma el_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 251) (hh : s.halted = false)
    (hb0 : s.core.ptrs 14 ≤ s.core.ptrs 16) :
    (run Q s detTape 1).core.pc = off + 397 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Add the term of `(v, j)`. -/
lemma eld (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (gv : ℝ) (s : State)
    (hpc : s.core.pc = off + 397) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 44 + s.core.ptrs 36) = gv) :
    (run Q s detTape 6).core.pc = off + 241 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 11 = s.core.ptrs 44 + s.core.ptrs 36 ∧
      (run Q s detTape 6).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 20 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 0 = (gv * s.core.regs 18) ∧
      (run Q s detTape 6).core.regs 13 = (s.core.regs 13 + (gv * s.core.regs 18)) ∧
      (∀ x, x ≠ 0 → x ≠ 13 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_preB6 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 44 + ptrs 36 → mem z = gv := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- Start the fixed part. -/
lemma el_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 251) (hh : s.halted = false)
    (hb0 : s.core.ptrs 16 < s.core.ptrs 14) :
    (run Q s detTape 4).core.pc = off + 255 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 18 = 0 ∧
      (run Q s detTape 4).core.ptrs 52 = s.core.ptrs 24 + s.core.ptrs 20 ∧
      (∀ x, x ≠ 18 → x ≠ 52 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs 19 = (0 : ℝ) ∧
      (∀ x, x ≠ 19 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- A fixed sign. -/
lemma ef_fix (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hv vv sv : ℝ) (s : State)
    (hpc : s.core.pc = off + 255) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 52) = hv)
    (fr1 : s.core.mem (s.core.ptrs 51 + s.core.ptrs 18) = vv)
    (fr2 : s.core.mem (s.core.ptrs 15 - s.core.ptrs 17 - s.core.ptrs 18) = sv)
    (hb0 : s.core.ptrs 18 < s.core.ptrs 3)
    (hb1 : s.core.ptrs 17 + s.core.ptrs 18 ≤ s.core.ptrs 48) :
    (run Q s detTape 15).core.pc = off + 255 ∧
      (run Q s detTape 15).halted = false ∧
      (run Q s detTape 15).core.ptrs 11 = s.core.ptrs 15 - s.core.ptrs 17 - s.core.ptrs 18 ∧
      (run Q s detTape 15).core.ptrs 18 = s.core.ptrs 18 + 1 ∧
      (run Q s detTape 15).core.ptrs 19 = s.core.ptrs 17 + s.core.ptrs 18 ∧
      (run Q s detTape 15).core.ptrs 52 = s.core.ptrs 52 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 11 → x ≠ 18 → x ≠ 19 → x ≠ 52 → (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 15).core.regs 0 = sv ∧
      (run Q s detTape 15).core.regs 19 = (s.core.regs 19 + ((hv * vv) * sv)) ∧
      (run Q s detTape 15).core.regs 20 = ((hv * vv) * sv) ∧
      (run Q s detTape 15).core.regs 21 = hv ∧
      (∀ x, x ≠ 0 → x ≠ 19 → x ≠ 20 → x ≠ 21 → (run Q s detTape 15).core.regs x = s.core.regs x) ∧
      (run Q s detTape 15).core.mem = s.core.mem ∧
      (run Q s detTape 15).integerMemory = s.integerMemory ∧
      (run Q s detTape 15).work = s.work + 15 ∧
      cellsWritten Q s 15 = ∅ := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 fr2 hb0 hb1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 52 → mem z = hv := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 51 + ptrs 18 → mem z = vv := fun z hz => hz ▸ fr1
  have er2 : ∀ z, z = ptrs 15 - ptrs 17 - ptrs 18 → mem z = sv := fun z hz => hz ▸ fr2
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- A free sign. -/
lemma ef_free (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 255) (hh : s.halted = false)
    (hb0 : s.core.ptrs 18 < s.core.ptrs 3)
    (hb1 : s.core.ptrs 48 < s.core.ptrs 17 + s.core.ptrs 18) :
    (run Q s detTape 9).core.pc = off + 255 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 18 = s.core.ptrs 18 + 1 ∧
      (run Q s detTape 9).core.ptrs 19 = s.core.ptrs 17 + s.core.ptrs 18 ∧
      (run Q s detTape 9).core.ptrs 52 = s.core.ptrs 52 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 18 → x ≠ 19 → x ≠ 52 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs 19 = (s.core.regs 19 + (0 : ℝ)) ∧
      (run Q s detTape 9).core.regs 20 = (0 : ℝ) ∧
      (∀ x, x ≠ 19 → x ≠ 20 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧
      (run Q s detTape 9).core.mem = s.core.mem ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      cellsWritten Q s 9 = ∅ := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma ef_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 255) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 18) :
    (run Q s detTape 3).core.pc = off + 273 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 5 = 0 ∧
      (∀ x, x ≠ 5 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs 0 = (1 : ℝ) ∧
      (∀ x, x ≠ 0 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma c0_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (fv : ℝ) (s : State)
    (hpc : s.core.pc = off + 273) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 5) = fv)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 39) :
    (run Q s detTape 9).core.pc = off + 273 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 9).core.ptrs 11 = s.core.ptrs 41 + s.core.ptrs 5 ∧
      (∀ x, x ≠ 5 → x ≠ 11 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs 0 = (s.core.regs 0 * s.core.regs 19) ∧
      (run Q s detTape 9).core.regs 1 = (s.core.regs 0 / fv) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧
      (run Q s detTape 9).core.mem (s.core.ptrs 41 + s.core.ptrs 5) = (s.core.regs 0 / fv) ∧
      (∀ z, z ≠ s.core.ptrs 41 + s.core.ptrs 5 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 41 + s.core.ptrs 5) := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 40 + ptrs 5 → mem z = fv := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma c0_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 273) (hh : s.halted = false)
    (hb0 : s.core.ptrs 39 ≤ s.core.ptrs 5) :
    (run Q s detTape 1).core.pc = off + 282 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

lemma c0d (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 282) (hh : s.halted = false) :
    (run Q s detTape 2).core.pc = off + 284 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 18 = 0 ∧
      (run Q s detTape 2).core.ptrs 52 = s.core.ptrs 24 + s.core.ptrs 20 ∧
      (∀ x, x ≠ 18 → x ≠ 52 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- A fixed sign: `a = 0`. -/
lemma er_fix (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 284) (hh : s.halted = false)
    (hb0 : s.core.ptrs 18 < s.core.ptrs 3)
    (hb1 : s.core.ptrs 17 + s.core.ptrs 18 ≤ s.core.ptrs 48) :
    (run Q s detTape 5).core.pc = off + 293 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 19 = s.core.ptrs 17 + s.core.ptrs 18 ∧
      (run Q s detTape 5).core.ptrs 53 = 0 ∧
      (∀ x, x ≠ 19 → x ≠ 53 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs 22 = (0 : ℝ) ∧
      (∀ x, x ≠ 22 → (run Q s detTape 5).core.regs x = s.core.regs x) ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- A free sign: `a = h·v`. -/
lemma er_free (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hv vv : ℝ) (s : State)
    (hpc : s.core.pc = off + 284) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 52) = hv)
    (fr1 : s.core.mem (s.core.ptrs 51 + s.core.ptrs 18) = vv)
    (hb0 : s.core.ptrs 18 < s.core.ptrs 3)
    (hb1 : s.core.ptrs 48 < s.core.ptrs 17 + s.core.ptrs 18) :
    (run Q s detTape 9).core.pc = off + 293 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 11 = s.core.ptrs 51 + s.core.ptrs 18 ∧
      (run Q s detTape 9).core.ptrs 19 = s.core.ptrs 17 + s.core.ptrs 18 ∧
      (run Q s detTape 9).core.ptrs 53 = 0 ∧
      (∀ x, x ≠ 11 → x ≠ 19 → x ≠ 53 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs 0 = vv ∧
      (run Q s detTape 9).core.regs 21 = hv ∧
      (run Q s detTape 9).core.regs 22 = (hv * vv) ∧
      (∀ x, x ≠ 0 → x ≠ 21 → x ≠ 22 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧
      (run Q s detTape 9).core.mem = s.core.mem ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      cellsWritten Q s 9 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 hb1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 52 → mem z = hv := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 51 + ptrs 18 → mem z = vv := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma er_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 284) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 18) :
    (run Q s detTape 1).core.pc = off + 330 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

lemma erd (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 330) (hh : s.halted = false) :
    (run Q s detTape 1).core.pc = off + 331 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 56 = 0 ∧
      (∀ x, x ≠ 56 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma em_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 293) (hh : s.halted = false)
    (hb0 : s.core.ptrs 53 < s.core.ptrs 39) :
    (run Q s detTape 7).core.pc = off + 300 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 5 = 0 ∧
      (run Q s detTape 7).core.ptrs 54 = 0 ∧
      (run Q s detTape 7).core.ptrs 55 = s.core.ptrs 53 + 1 ∧
      (∀ x, x ≠ 5 → x ≠ 54 → x ≠ 55 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 23 = (0 : ℝ) ∧
      (run Q s detTape 7).core.regs 24 = (1 : ℝ) ∧
      (∀ x, x ≠ 23 → x ≠ 24 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma em_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 293) (hh : s.halted = false)
    (hb0 : s.core.ptrs 39 ≤ s.core.ptrs 53) :
    (run Q s detTape 2).core.pc = off + 320 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 5 = 0 ∧
      (∀ x, x ≠ 5 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma et_even (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (fv cv : ℝ) (s : State)
    (hpc : s.core.pc = off + 300) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 5) = fv)
    (fr1 : s.core.mem (s.core.ptrs 41 + s.core.ptrs 53 - s.core.ptrs 5) = cv)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 55)
    (hb1 : s.core.ptrs 54 ≤ s.core.ptrs 0) :
    (run Q s detTape 14).core.pc = off + 300 ∧
      (run Q s detTape 14).halted = false ∧
      (run Q s detTape 14).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 14).core.ptrs 11 = s.core.ptrs 41 + s.core.ptrs 53 - s.core.ptrs 5 ∧
      (run Q s detTape 14).core.ptrs 54 = s.core.ptrs 1 - s.core.ptrs 54 ∧
      (∀ x, x ≠ 5 → x ≠ 11 → x ≠ 54 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 14).core.regs 0 = cv ∧
      (run Q s detTape 14).core.regs 1 = ((s.core.regs 24 / fv) * cv) ∧
      (run Q s detTape 14).core.regs 23 = (s.core.regs 23 + ((s.core.regs 24 / fv) * cv)) ∧
      (run Q s detTape 14).core.regs 24 = (s.core.regs 24 * s.core.regs 22) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 23 → x ≠ 24 → (run Q s detTape 14).core.regs x = s.core.regs x) ∧
      (run Q s detTape 14).core.mem = s.core.mem ∧
      (run Q s detTape 14).integerMemory = s.integerMemory ∧
      (run Q s detTape 14).work = s.work + 14 ∧
      cellsWritten Q s 14 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 hb1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 40 + ptrs 5 → mem z = fv := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 41 + ptrs 53 - ptrs 5 → mem z = cv := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma et_odd (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 300) (hh : s.halted = false)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 55)
    (hb1 : s.core.ptrs 0 < s.core.ptrs 54) :
    (run Q s detTape 7).core.pc = off + 300 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 7).core.ptrs 54 = s.core.ptrs 1 - s.core.ptrs 54 ∧
      (∀ x, x ≠ 5 → x ≠ 54 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 24 = (s.core.regs 24 * s.core.regs 22) ∧
      (∀ x, x ≠ 24 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma et_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 300) (hh : s.halted = false)
    (hb0 : s.core.ptrs 55 ≤ s.core.ptrs 5) :
    (run Q s detTape 5).core.pc = off + 293 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 11 = s.core.ptrs 42 + s.core.ptrs 53 ∧
      (run Q s detTape 5).core.ptrs 53 = s.core.ptrs 53 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 53 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 42 + s.core.ptrs 53) = s.core.regs 23 ∧
      (∀ z, z ≠ s.core.ptrs 42 + s.core.ptrs 53 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 42 + s.core.ptrs 53) := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma cp_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (tv : ℝ) (s : State)
    (hpc : s.core.pc = off + 320) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 42 + s.core.ptrs 5) = tv)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 39) :
    (run Q s detTape 7).core.pc = off + 320 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 7).core.ptrs 11 = s.core.ptrs 41 + s.core.ptrs 5 ∧
      (∀ x, x ≠ 5 → x ≠ 11 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 0 = tv ∧
      (∀ x, x ≠ 0 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem (s.core.ptrs 41 + s.core.ptrs 5) = tv ∧
      (∀ z, z ≠ s.core.ptrs 41 + s.core.ptrs 5 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 41 + s.core.ptrs 5) := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 42 + ptrs 5 → mem z = tv := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma cp_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 320) (hh : s.halted = false)
    (hb0 : s.core.ptrs 39 ≤ s.core.ptrs 5) :
    (run Q s detTape 4).core.pc = off + 284 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 18 = s.core.ptrs 18 + 1 ∧
      (run Q s detTape 4).core.ptrs 52 = s.core.ptrs 52 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 18 → x ≠ 52 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma ek_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 331) (hh : s.halted = false)
    (hb0 : s.core.ptrs 56 < s.core.ptrs 37) :
    (run Q s detTape 5).core.pc = off + 336 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 10 = 0 ∧
      (run Q s detTape 5).core.ptrs 57 = s.core.ptrs 56 + 1 ∧
      (∀ x, x ≠ 10 → x ≠ 57 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs 23 = (0 : ℝ) ∧
      (∀ x, x ≠ 23 → (run Q s detTape 5).core.regs x = s.core.regs x) ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma ek_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 331) (hh : s.halted = false)
    (hb0 : s.core.ptrs 37 ≤ s.core.ptrs 56) :
    (run Q s detTape 2).core.pc = off + 367 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 53 = 0 ∧
      (∀ x, x ≠ 53 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma ei_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (f1 f2 f3 pv f4 cv : ℝ) (s : State)
    (hpc : s.core.pc = off + 336) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 56) = f1)
    (fr1 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 10) = f2)
    (fr2 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 56 - s.core.ptrs 10) = f3)
    (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 56 - s.core.ptrs 10) = pv)
    (fr4 : s.core.mem (s.core.ptrs 40 + 2 * s.core.ptrs 10) = f4)
    (fr5 : s.core.mem (s.core.ptrs 41 + 2 * s.core.ptrs 10) = cv)
    (hb0 : s.core.ptrs 10 < s.core.ptrs 57) :
    (run Q s detTape 23).core.pc = off + 336 ∧
      (run Q s detTape 23).halted = false ∧
      (run Q s detTape 23).core.ptrs 10 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 23).core.ptrs 11 = s.core.ptrs 41 + 2 * s.core.ptrs 10 ∧
      (run Q s detTape 23).core.ptrs 12 = s.core.ptrs 56 - s.core.ptrs 10 ∧
      (run Q s detTape 23).core.ptrs 58 = 2 * s.core.ptrs 10 ∧
      (∀ x, x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 58 → (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 23).core.regs 0 = (((((f1 / f2) / f3) * pv) * f4) * cv) ∧
      (run Q s detTape 23).core.regs 1 = cv ∧
      (run Q s detTape 23).core.regs 23 = (s.core.regs 23 + (((((f1 / f2) / f3) * pv) * f4) * cv)) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 23 → (run Q s detTape 23).core.regs x = s.core.regs x) ∧
      (run Q s detTape 23).core.mem = s.core.mem ∧
      (run Q s detTape 23).integerMemory = s.integerMemory ∧
      (run Q s detTape 23).work = s.work + 23 ∧
      cellsWritten Q s 23 = ∅ := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 fr2 fr3 fr4 fr5 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 40 + ptrs 56 → mem z = f1 := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 40 + ptrs 10 → mem z = f2 := fun z hz => hz ▸ fr1
  have er2 : ∀ z, z = ptrs 40 + ptrs 56 - ptrs 10 → mem z = f3 := fun z hz => hz ▸ fr2
  have er3 : ∀ z, z = ptrs 43 + ptrs 56 - ptrs 10 → mem z = pv := fun z hz => hz ▸ fr3
  have er4 : ∀ z, z = ptrs 40 + 2 * ptrs 10 → mem z = f4 := fun z hz => hz ▸ fr4
  have er5 : ∀ z, z = ptrs 41 + 2 * ptrs 10 → mem z = cv := fun z hz => hz ▸ fr5
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3, er4, er5]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3, er4, er5]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3, er4, er5]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3, er4, er5]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3, er4, er5]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3, er4, er5]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma ei_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (f1 : ℝ) (s : State)
    (hpc : s.core.pc = off + 336) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 40 + s.core.ptrs 56) = f1)
    (hb0 : s.core.ptrs 57 ≤ s.core.ptrs 10) :
    (run Q s detTape 8).core.pc = off + 331 ∧
      (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 11 = s.core.ptrs 46 + s.core.ptrs 56 ∧
      (run Q s detTape 8).core.ptrs 56 = s.core.ptrs 56 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 56 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs 1 = f1 ∧
      (run Q s detTape 8).core.regs 23 = (s.core.regs 23 / f1) ∧
      (∀ x, x ≠ 1 → x ≠ 23 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧
      (run Q s detTape 8).core.mem (s.core.ptrs 46 + s.core.ptrs 56) = (s.core.regs 23 / f1) ∧
      (∀ z, z ≠ s.core.ptrs 46 + s.core.ptrs 56 → (run Q s detTape 8).core.mem z = s.core.mem z) ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧
      ∀ c ∈ cellsWritten Q s 8, c = (true, s.core.ptrs 46 + s.core.ptrs 56) := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 40 + ptrs 56 → mem z = f1 := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma gm_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 367) (hh : s.halted = false)
    (hb0 : s.core.ptrs 53 < s.core.ptrs 37) :
    (run Q s detTape 5).core.pc = off + 372 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 5 = 0 ∧
      (run Q s detTape 5).core.ptrs 55 = s.core.ptrs 53 + 1 ∧
      (∀ x, x ≠ 5 → x ≠ 55 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs 23 = (0 : ℝ) ∧
      (∀ x, x ≠ 23 → (run Q s detTape 5).core.regs x = s.core.regs x) ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma gm_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 367) (hh : s.halted = false)
    (hb0 : s.core.ptrs 37 ≤ s.core.ptrs 53) :
    (run Q s detTape 2).core.pc = off + 387 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 5 = 0 ∧
      (∀ x, x ≠ 5 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma gt_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (gv ev : ℝ) (s : State)
    (hpc : s.core.pc = off + 372) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 44 + s.core.ptrs 5) = gv)
    (fr1 : s.core.mem (s.core.ptrs 46 + s.core.ptrs 53 - s.core.ptrs 5) = ev)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 55) :
    (run Q s detTape 10).core.pc = off + 372 ∧
      (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 10).core.ptrs 11 = s.core.ptrs 46 + s.core.ptrs 53 - s.core.ptrs 5 ∧
      (run Q s detTape 10).core.ptrs 12 = s.core.ptrs 53 - s.core.ptrs 5 ∧
      (∀ x, x ≠ 5 → x ≠ 11 → x ≠ 12 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs 0 = (gv * ev) ∧
      (run Q s detTape 10).core.regs 1 = ev ∧
      (run Q s detTape 10).core.regs 23 = (s.core.regs 23 + (gv * ev)) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 23 → (run Q s detTape 10).core.regs x = s.core.regs x) ∧
      (run Q s detTape 10).core.mem = s.core.mem ∧
      (run Q s detTape 10).integerMemory = s.integerMemory ∧
      (run Q s detTape 10).work = s.work + 10 ∧
      cellsWritten Q s 10 = ∅ := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 44 + ptrs 5 → mem z = gv := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 46 + ptrs 53 - ptrs 5 → mem z = ev := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma gt_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 372) (hh : s.halted = false)
    (hb0 : s.core.ptrs 55 ≤ s.core.ptrs 5) :
    (run Q s detTape 5).core.pc = off + 367 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 11 = s.core.ptrs 45 + s.core.ptrs 53 ∧
      (run Q s detTape 5).core.ptrs 53 = s.core.ptrs 53 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 53 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 45 + s.core.ptrs 53) = s.core.regs 23 ∧
      (∀ z, z ≠ s.core.ptrs 45 + s.core.ptrs 53 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 45 + s.core.ptrs 53) := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma gc_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (tv : ℝ) (s : State)
    (hpc : s.core.pc = off + 387) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 45 + s.core.ptrs 5) = tv)
    (hb0 : s.core.ptrs 5 < s.core.ptrs 37) :
    (run Q s detTape 7).core.pc = off + 387 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 5 = s.core.ptrs 5 + 1 ∧
      (run Q s detTape 7).core.ptrs 11 = s.core.ptrs 44 + s.core.ptrs 5 ∧
      (∀ x, x ≠ 5 → x ≠ 11 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 0 = tv ∧
      (∀ x, x ≠ 0 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem (s.core.ptrs 44 + s.core.ptrs 5) = tv ∧
      (∀ z, z ≠ s.core.ptrs 44 + s.core.ptrs 5 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 44 + s.core.ptrs 5) := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 45 + ptrs 5 → mem z = tv := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma gc_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 387) (hh : s.halted = false)
    (hb0 : s.core.ptrs 37 ≤ s.core.ptrs 5) :
    (run Q s detTape 4).core.pc = off + 251 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 16 = s.core.ptrs 16 + 1 ∧
      (run Q s detTape 4).core.ptrs 17 = s.core.ptrs 17 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 16 → x ≠ 17 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB5 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

end DetANN.Supplement.Thm32

-- ===== T32_EvalMath =====
namespace DetANN.Supplement.Thm32

open DetANN Finset

lemma coeff_egf (m : ℕ → ℝ) (k : ℕ) : PowerSeries.coeff k (egf m) = m k / (k.factorial : ℝ) := by
  simp [egf, PowerSeries.coeff_mk]

lemma coeff_exp (c : ℝ) (k : ℕ) : PowerSeries.coeff k (expSeries c) = c ^ k / (k.factorial : ℝ) :=
  coeff_egf _ _

lemma coeff_cosh (a : ℝ) (k : ℕ) :
    PowerSeries.coeff k (coshSeries a) = (if Even k then a ^ k else 0) / (k.factorial : ℝ) :=
  coeff_egf _ _

lemma coeff_mul_range (A B : PowerSeries ℝ) (m : ℕ) :
    PowerSeries.coeff m (A * B) =
      ∑ i ∈ range (m + 1), PowerSeries.coeff i A * PowerSeries.coeff (m - i) B := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i A * PowerSeries.coeff j B)]

/-- One term of the inner `cosh` loop: `[i even] aⁱ/i! · C(m-i)`. -/
noncomputable def coshTerm (a : ℝ) (C : ℕ → ℝ) (m i : ℕ) : ℝ :=
  if i % 2 = 0 then a ^ i / (i.factorial : ℝ) * C (m - i) else 0

lemma cosh_step (a : ℝ) (S : PowerSeries ℝ) (C : ℕ → ℝ) (m : ℕ)
    (hC : ∀ i, i ≤ m → C i = PowerSeries.coeff i S) :
    ∑ i ∈ range (m + 1), coshTerm a C m i = PowerSeries.coeff m (S * coshSeries a) := by
  rw [mul_comm, coeff_mul_range]
  apply sum_congr rfl
  intro i hi
  have him : i ≤ m := by simp at hi; omega
  unfold coshTerm
  rw [coeff_cosh, hC (m - i) (by omega)]
  by_cases h : i % 2 = 0
  · have he : Even i := Nat.even_iff.2 h
    rw [if_pos h, if_pos he]
  · have he : ¬ Even i := fun e => h (Nat.even_iff.1 e)
    rw [if_neg h, if_neg he]; simp

/-- One term of the moment loop: `κ!/i!/(κ-i)! · PN(κ-i) · (2i)! · C(2i)`. -/
noncomputable def momTerm (PN Cf : ℕ → ℝ) (κ i : ℕ) : ℝ :=
  (κ.factorial : ℝ) / (i.factorial : ℝ) / ((κ - i).factorial : ℝ) * PN (κ - i) *
    ((2 * i).factorial : ℝ) * Cf (2 * i)

lemma choose_real {κ i : ℕ} (h : i ≤ κ) :
    (κ.factorial : ℝ) / (i.factorial : ℝ) / ((κ - i).factorial : ℝ) = (κ.choose i : ℝ) := by
  have e := Nat.choose_mul_factorial_mul_factorial h
  have h1 : (0 : ℝ) < i.factorial := by exact_mod_cast Nat.factorial_pos i
  have h2 : (0 : ℝ) < (κ - i).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_div, div_eq_iff (by positivity)]
  exact_mod_cast e.symm.trans (by ring)

/-- The exponential generating function of `X = Y² - nv` from the series `S` of `Y`. -/
noncomputable def xSeries (nv : ℝ) (S : PowerSeries ℝ) : PowerSeries ℝ :=
  egf fun k => ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (-nv) ^ (k - i) *
    ((2 * i).factorial : ℝ) * PowerSeries.coeff (2 * i) S

lemma mom_step (nv : ℝ) (S : PowerSeries ℝ) (PN Cf : ℕ → ℝ) (κ : ℕ)
    (hPN : ∀ j, j ≤ κ → PN j = (-nv) ^ j)
    (hC : ∀ i, i ≤ κ → Cf (2 * i) = PowerSeries.coeff (2 * i) S) :
    (∑ i ∈ range (κ + 1), momTerm PN Cf κ i) / (κ.factorial : ℝ) =
      PowerSeries.coeff κ (xSeries nv S) := by
  unfold xSeries
  rw [coeff_egf]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hik : i ≤ κ := by simp at hi; omega
  unfold momTerm
  rw [choose_real hik, hPN (κ - i) (by omega), hC i hik]

lemma prod_step (A B : PowerSeries ℝ) (G E : ℕ → ℝ) (m : ℕ)
    (hG : ∀ i, i ≤ m → G i = PowerSeries.coeff i A) (hE : ∀ i, i ≤ m → E i = PowerSeries.coeff i B) :
    ∑ i ∈ range (m + 1), G i * E (m - i) = PowerSeries.coeff m (A * B) := by
  rw [coeff_mul_range]
  apply sum_congr rfl
  intro i hi
  have him : i ≤ m := by simp at hi; omega
  rw [hG i him, hE (m - i) (by omega)]

lemma prod_lt_succ {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) (t : ℕ) (ht : t < n) :
    ∏ x ∈ univ.filter (fun x : Fin n => (x : ℕ) < t + 1), f x =
      (∏ x ∈ univ.filter (fun x : Fin n => (x : ℕ) < t), f x) * f ⟨t, ht⟩ := by
  have e : univ.filter (fun x : Fin n => (x : ℕ) < t + 1) =
      insert ⟨t, ht⟩ (univ.filter (fun x : Fin n => (x : ℕ) < t)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
  rw [e, prod_insert (by simp), mul_comm]

lemma sum_lt_succ {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (t : ℕ) (ht : t < n) :
    ∑ x ∈ univ.filter (fun x : Fin n => (x : ℕ) < t + 1), f x =
      (∑ x ∈ univ.filter (fun x : Fin n => (x : ℕ) < t), f x) + f ⟨t, ht⟩ := by
  have e : univ.filter (fun x : Fin n => (x : ℕ) < t + 1) =
      insert ⟨t, ht⟩ (univ.filter (fun x : Fin n => (x : ℕ) < t)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
  rw [e, sum_insert (by simp), add_comm]

lemma prod_lt_zero {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    ∏ x ∈ univ.filter (fun x : Fin n => (x : ℕ) < 0), f x = 1 := by
  rw [show univ.filter (fun x : Fin n => (x : ℕ) < 0) = ∅ by ext x; simp]; rfl

lemma sum_lt_zero {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) :
    ∑ x ∈ univ.filter (fun x : Fin n => (x : ℕ) < 0), f x = 0 := by
  rw [show univ.filter (fun x : Fin n => (x : ℕ) < 0) = ∅ by ext x; simp]; rfl

lemma prod_lt_all {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    ∏ x ∈ univ.filter (fun x : Fin n => (x : ℕ) < n), f x = ∏ x, f x := by
  rw [filter_true_of_mem (fun x _ => x.isLt)]

lemma sum_lt_all {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) :
    ∑ x ∈ univ.filter (fun x : Fin n => (x : ℕ) < n), f x = ∑ x, f x := by
  rw [filter_true_of_mem (fun x _ => x.isLt)]

/-- The series of `Y_{ℓ,j,v}` after the first `t` coordinates. -/
noncomputable def ySer {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ u : Fin L → Fin d → Bool) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (ℓ : Fin L) (t : ℕ) : PowerSeries ℝ :=
  expSeries (fixedPart h μ u j v ℓ) *
    ∏ r ∈ univ.filter (fun r : Fin d => (r : ℕ) < t), coshSeries (freeCoeff h μ j v ℓ r)

/-- The product over the first `t` repetitions. -/
noncomputable def gSer {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ u : Fin L → Fin d → Bool) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (t : ℕ) : PowerSeries ℝ :=
  ∏ ℓ ∈ univ.filter (fun ℓ : Fin L => (ℓ : ℕ) < t), xSeries (‖v‖ ^ 2) (ySer h μ u j v ℓ d)

/-- The term of `(v, j)` in `lemma62Expr`. -/
noncomputable def termVJ {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (p₀ : ℕ)
    (μ u : Fin L → Fin d → Bool) (v : EuclideanSpace ℝ (Fin d)) (j : Fin d) : ℝ :=
  (((L : ℝ) * τ * ‖v‖ ^ 2) ^ (2 * p₀))⁻¹ * ((2 * p₀).factorial : ℝ) *
    PowerSeries.coeff (2 * p₀) (gSer h μ u j v L)

lemma lemma62_eq {d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (L : ℕ) (τ : ℝ) (p₀ : ℕ)
    (l : List (EuclideanSpace ℝ (Fin d))) (hl : l.Nodup) (μ u : Fin L → Fin d → Bool) :
    lemma62Expr h L τ p₀ l.toFinset μ u = (l.map fun v => ∑ j : Fin d, termVJ h τ p₀ μ u v j).sum := by
  unfold lemma62Expr
  rw [List.sum_toFinset _ hl]
  congr 1
  apply List.map_congr_left
  intro v _
  apply sum_congr rfl
  intro j _
  unfold termVJ gSer ySer xSeries
  rw [prod_lt_all]
  congr 3
  funext ℓ
  rw [prod_lt_all]

end DetANN.Supplement.Thm32

-- ===== T32_EvalA =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP Finset

/-- From `s` to `s'` only the pointers in `Wp`, the reals in `Wr` and the cells in `Wm` change. -/
def Fr (Wp Wr : Finset ℕ) (Wm : ℤ → Prop) (s s' : State) : Prop :=
  (∀ y, y ∉ Wp → s'.core.ptrs y = s.core.ptrs y) ∧ (∀ y, y ∉ Wr → s'.core.regs y = s.core.regs y) ∧
    (∀ z, ¬ Wm z → s'.core.mem z = s.core.mem z) ∧ s'.integerMemory = s.integerMemory

lemma fr_refl (Wp Wr : Finset ℕ) (Wm : ℤ → Prop) (s : State) : Fr Wp Wr Wm s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

lemma fr_trans {Wp Wr : Finset ℕ} {Wm : ℤ → Prop} {s1 s2 s3 : State} (h1 : Fr Wp Wr Wm s1 s2)
    (h2 : Fr Wp Wr Wm s2 s3) : Fr Wp Wr Wm s1 s3 :=
  ⟨fun y hy => (h2.1 y hy).trans (h1.1 y hy), fun y hy => (h2.2.1 y hy).trans (h1.2.1 y hy),
    fun z hz => (h2.2.2.1 z hz).trans (h1.2.2.1 z hz), h2.2.2.2.trans h1.2.2.2⟩

lemma fr_mono {Wp Wr Wp' Wr' : Finset ℕ} {Wm Wm' : ℤ → Prop} {s s' : State} (h : Fr Wp Wr Wm s s')
    (hp : Wp ⊆ Wp') (hr : Wr ⊆ Wr') (hm : ∀ z, Wm z → Wm' z) : Fr Wp' Wr' Wm' s s' :=
  ⟨fun y hy => h.1 y (fun e => hy (hp e)), fun y hy => h.2.1 y (fun e => hy (hr e)),
    fun z hz => h.2.2.1 z (fun e => hz (hm z e)), h.2.2.2⟩

lemma loop_inv {Q : Program} {H : ℕ} (Inv : ℕ → State → Prop) (n B : ℕ)
    (hstep : ∀ t s, t < n → Inv t s → s.core.pc = H → s.halted = false →
      ∃ u, u ≤ B ∧ (run Q s detTape u).core.pc = H ∧ (run Q s detTape u).halted = false ∧
        (run Q s detTape u).work = s.work + u ∧ Inv (t + 1) (run Q s detTape u)) :
    ∀ k t s, t + k = n → Inv t s → s.core.pc = H → s.halted = false →
      ∃ u, u ≤ k * B ∧ (run Q s detTape u).core.pc = H ∧ (run Q s detTape u).halted = false ∧
        (run Q s detTape u).work = s.work + u ∧ Inv n (run Q s detTape u) := by
  intro k
  induction k with
  | zero =>
    intro t s h hI hpc hh
    have : t = n := by omega
    subst this
    exact ⟨0, by simp, by rw [run_zero]; exact hpc, by rw [run_zero]; exact hh, by rw [run_zero]; rfl,
      by rw [run_zero]; exact hI⟩
  | succ k ih =>
    intro t s h hI hpc hh
    obtain ⟨u, hu, a1, a2, a3, a4⟩ := hstep t s (by omega) hI hpc hh
    obtain ⟨u', hu', b1, b2, b3, b4⟩ := ih (t + 1) _ (by omega) a4 a1 a2
    refine ⟨u + u', by rw [Nat.succ_mul]; omega, ?_⟩
    rw [run_add]
    exact ⟨b1, b2, by rw [b3, a3]; ring, b4⟩

lemma n2_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (d : ℕ) (vb : ℤ)
    (vf : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 211) (hh : s.halted = false)
    (h3 : s.core.ptrs 3 = d) (h51 : s.core.ptrs 51 = vb) (h31 : s.core.ptrs 31 = 0)
    (h14 : s.core.regs 14 = 0) (hv : ∀ c : ℕ, c < d → s.core.mem (vb + c) = vf c) :
    ∃ u, u ≤ d * 7 + 4 ∧ (run Q s detTape u).core.pc = off + 221 ∧ (run Q s detTape u).halted = false ∧
      (run Q s detTape u).work = s.work + u ∧
      (run Q s detTape u).core.regs 14 = ∑ c ∈ range d, vf c * vf c ∧
      (run Q s detTape u).core.regs 15 = s.core.regs 6 - ∑ c ∈ range d, vf c * vf c ∧
      (run Q s detTape u).core.regs 0 = 1 ∧ (run Q s detTape u).core.ptrs 5 = 0 ∧
      Fr {5, 11, 31} {0, 14, 15} (fun _ => False) s (run Q s detTape u) := by
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 31 = t ∧
    s'.core.regs 14 = ∑ c ∈ range t, vf c * vf c ∧ Fr {11, 31} {0, 14} (fun _ => False) s s'
  have hst : ∀ t s', t < d → Inv t s' → s'.core.pc = off + 211 → s'.halted = false →
      ∃ u, u ≤ 7 ∧ (run Q s' detTape u).core.pc = off + 211 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have e51 : s'.core.ptrs 51 = vb := by rw [i3.1 51 (by decide), h51]
    have e3 : s'.core.ptrs 3 = d := by rw [i3.1 3 (by decide), h3]
    obtain ⟨g1, g2, _, g4, g5, _, g7, g8, g9, g10, g11, _⟩ :=
      n2_step Q off q hE (vf t) s' hpc' hh' (by rw [e51, i1, i3.2.2.1 _ (fun h => h)]; exact hv t ht)
        (by rw [i1, e3]; exact_mod_cast ht)
    refine ⟨7, le_rfl, g1, g2, g11, by rw [g4, i1]; push_cast; ring, by rw [g7, i2, sum_range_succ], ?_⟩
    exact fr_trans i3 ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun y hy => g8 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun z _ => by rw [g9], g10⟩
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv d 7 hst d 0 s (by omega) ⟨by rw [h31]; rfl, by rw [h14]; simp, fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
    n2_exit Q off q hE _ a1 a2 (by rw [b1, b3.1 3 (by decide), h3])
  refine ⟨u + 4, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g10, a3]; ring, by rw [g7 14 (by decide) (by decide), b2],
    by rw [g6, b2, b3.2.1 6 (by decide)], g5, g3, ?_⟩
  exact fr_trans (fr_mono b3 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => g4 y (by rintro rfl; exact hy (by decide)),
      fun y hy => g7 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun z _ => by rw [g8], g9⟩

lemma pn_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (P1 : ℕ) (PNb : ℤ)
    (s : State) (hpc : s.core.pc = off + 221) (hh : s.halted = false)
    (h37 : s.core.ptrs 37 = P1) (h43 : s.core.ptrs 43 = PNb) (h5 : s.core.ptrs 5 = 0)
    (h0 : s.core.regs 0 = 1) :
    ∃ u, u ≤ P1 * 6 + 6 ∧ (run Q s detTape u).core.pc = off + 232 ∧ (run Q s detTape u).halted = false ∧
      (run Q s detTape u).work = s.work + u ∧
      (∀ i : ℕ, i < P1 → (run Q s detTape u).core.mem (PNb + i) = s.core.regs 15 ^ i) ∧
      (run Q s detTape u).core.regs 16 = ((s.core.ptrs 14 : ℤ) : ℝ) ∧
      (run Q s detTape u).core.regs 17 = ((s.core.ptrs 14 : ℤ) : ℝ) * s.core.regs 5 * s.core.regs 14 ∧
      (run Q s detTape u).core.regs 0 = 1 ∧ (run Q s detTape u).core.ptrs 5 = 0 ∧
      Fr {5, 11} {0, 16, 17} (fun z => PNb ≤ z ∧ z < PNb + P1) s (run Q s detTape u) := by
  let Wm : ℤ → Prop := fun z => PNb ≤ z ∧ z < PNb + P1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 5 = t ∧ s'.core.regs 0 = s.core.regs 15 ^ t ∧
    (∀ i : ℕ, i < t → s'.core.mem (PNb + i) = s.core.regs 15 ^ i) ∧ Fr {5, 11} {0} Wm s s'
  have hst : ∀ t s', t < P1 → Inv t s' → s'.core.pc = off + 221 → s'.halted = false →
      ∃ u, u ≤ 6 ∧ (run Q s' detTape u).core.pc = off + 221 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3, i4⟩ hpc' hh'
    have e43 : s'.core.ptrs 43 = PNb := by rw [i4.1 43 (by decide), h43]
    have e37 : s'.core.ptrs 37 = P1 := by rw [i4.1 37 (by decide), h37]
    have e15 : s'.core.regs 15 = s.core.regs 15 := i4.2.1 15 (by decide)
    obtain ⟨g1, g2, g3, _, g5, g6, g7, g8, g9, g10, g11, _⟩ :=
      pn_step Q off q hE s' hpc' hh' (by rw [i1, e37]; exact_mod_cast ht)
    rw [e43, i1] at g8 g9
    refine ⟨6, le_rfl, g1, g2, g11, by rw [g3, i1]; push_cast; ring, by rw [g6, i2, e15, pow_succ], ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge i t with h | h
      · have hne : PNb + (i : ℤ) ≠ PNb + (t : ℤ) := by
          intro e; have : (i : ℤ) = t := by linarith
          omega
        rw [g9 _ hne]
        exact i3 i h
      · have : i = t := by omega
        subst this; rw [g8, i2]
    · exact fr_trans i4 ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun y hy => g7 y (by rintro rfl; exact hy (by decide)),
        fun z hz => g9 z (by rintro rfl; exact hz ⟨by linarith, by push_cast; linarith⟩), g10⟩
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3, b4⟩ :=
    loop_inv (Q := Q) Inv P1 6 hst P1 0 s (by omega)
      ⟨by rw [h5]; rfl, by rw [h0]; simp, fun i h => absurd h (Nat.not_lt_zero _), fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, _⟩ :=
    pn_exit Q off q hE _ a1 a2 (by rw [b4.1 37 (by decide), h37, b1])
  refine ⟨u + 6, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g11, a3]; ring, fun i hi => by rw [g9]; exact b3 i hi,
    by rw [g6, b4.1 14 (by decide)],
    by rw [g7, b4.1 14 (by decide), b4.2.1 5 (by decide), b4.2.1 14 (by decide)], g5, g3, ?_⟩
  exact fr_trans (fr_mono b4 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => g4 y (by rintro rfl; exact hy (by decide)),
      fun y hy => g8 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
        (by rintro rfl; exact hy (by decide)),
      fun z _ => by rw [g9], g10⟩

lemma bp_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (P2 : ℕ) (Fb : ℤ) (fv : ℝ)
    (s : State) (hpc : s.core.pc = off + 232) (hh : s.halted = false)
    (h36 : s.core.ptrs 36 = P2) (h40 : s.core.ptrs 40 = Fb) (h5 : s.core.ptrs 5 = 0)
    (h0 : s.core.regs 0 = 1) (hfv : s.core.mem (Fb + P2) = fv) :
    ∃ u, u ≤ P2 * 4 + 6 ∧ (run Q s detTape u).core.pc = off + 241 ∧ (run Q s detTape u).halted = false ∧
      (run Q s detTape u).work = s.work + u ∧
      (run Q s detTape u).core.regs 18 = s.core.regs 7 / s.core.regs 17 ^ P2 * fv ∧
      (run Q s detTape u).core.ptrs 20 = 0 ∧
      Fr {5, 11, 20} {0, 1, 18} (fun _ => False) s (run Q s detTape u) := by
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 5 = t ∧ s'.core.regs 0 = s.core.regs 17 ^ t ∧
    Fr {5} {0} (fun _ => False) s s'
  have hst : ∀ t s', t < P2 → Inv t s' → s'.core.pc = off + 232 → s'.halted = false →
      ∃ u, u ≤ 4 ∧ (run Q s' detTape u).core.pc = off + 232 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      bp_step Q off q hE s' hpc' hh' (by rw [i1, i3.1 36 (by decide), h36]; exact_mod_cast ht)
    refine ⟨4, le_rfl, g1, g2, g9, by rw [g3, i1]; push_cast; ring,
      by rw [g5, i2, i3.2.1 17 (by decide), pow_succ], ?_⟩
    exact fr_trans i3 ⟨fun y hy => g4 y (by rintro rfl; exact hy (by decide)),
      fun y hy => g6 y (by rintro rfl; exact hy (by decide)), fun z _ => by rw [g7], g8⟩
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv P2 4 hst P2 0 s (by omega) ⟨by rw [h5]; rfl, by rw [h0]; simp, fr_refl _ _ _ _⟩
      hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, _⟩ :=
    bp_exit Q off q hE fv _ a1 a2
      (by rw [b3.1 40 (by decide), b3.1 36 (by decide), h40, h36, b3.2.2.1 _ (fun h => h)]; exact hfv)
      (by rw [b3.1 36 (by decide), h36, b1])
  refine ⟨u + 6, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g11, a3]; ring, by rw [g7, b2, b3.2.1 7 (by decide)], g4, ?_⟩
  exact fr_trans (fr_mono b3 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun y hy => g8 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun z _ => by rw [g9], g10⟩

lemma g0_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (P1 : ℕ) (hP1 : 1 ≤ P1)
    (Gb : ℤ) (s : State) (hpc : s.core.pc = off + 243) (hh : s.halted = false)
    (h37 : s.core.ptrs 37 = P1) (h44 : s.core.ptrs 44 = Gb) (h5 : s.core.ptrs 5 = 0)
    (h6 : s.core.regs 6 = 0) (h7 : s.core.regs 7 = 1) :
    ∃ u, u ≤ P1 * 5 + 4 ∧ (run Q s detTape u).core.pc = off + 251 ∧ (run Q s detTape u).halted = false ∧
      (run Q s detTape u).work = s.work + u ∧
      (∀ i : ℕ, i < P1 → (run Q s detTape u).core.mem (Gb + i) = if i = 0 then 1 else 0) ∧
      (run Q s detTape u).core.ptrs 16 = 0 ∧ (run Q s detTape u).core.ptrs 17 = 0 ∧
      Fr {5, 11, 16, 17} {} (fun z => Gb ≤ z ∧ z < Gb + P1) s (run Q s detTape u) := by
  let Wm : ℤ → Prop := fun z => Gb ≤ z ∧ z < Gb + P1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 5 = t ∧
    (∀ i : ℕ, i < t → s'.core.mem (Gb + i) = 0) ∧ Fr {5, 11} {} Wm s s'
  have hst : ∀ t s', t < P1 → Inv t s' → s'.core.pc = off + 243 → s'.halted = false →
      ∃ u, u ≤ 5 ∧ (run Q s' detTape u).core.pc = off + 243 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    obtain ⟨g1, g2, g3, _, g5, g6, g7, g8, g9, g10, _⟩ :=
      g0_step Q off q hE s' hpc' hh' (by rw [i1, i3.1 37 (by decide), h37]; exact_mod_cast ht)
    rw [i3.1 44 (by decide), h44, i1] at g7 g8
    refine ⟨5, le_rfl, g1, g2, g10, by rw [g3, i1]; push_cast; ring, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge i t with h | h
      · have hne : Gb + (i : ℤ) ≠ Gb + (t : ℤ) := by
          intro e; have : (i : ℤ) = t := by linarith
          omega
        rw [g8 _ hne]; exact i2 i h
      · have : i = t := by omega
        subst this; rw [g7, i3.2.1 6 (by decide), h6]
    · exact fr_trans i3 ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun y _ => by rw [g6], fun z hz => g8 z (by rintro rfl; exact hz ⟨by linarith, by push_cast; linarith⟩),
        g9⟩
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv P1 5 hst P1 0 s (by omega)
      ⟨by rw [h5]; rfl, fun i h => absurd h (Nat.not_lt_zero _), fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
    g0_exit Q off q hE _ a1 a2 (by rw [b3.1 37 (by decide), h37, b1])
  rw [b3.1 44 (by decide), h44] at g7 g8
  refine ⟨u + 4, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g10, a3]; ring, ?_, g3, g4, ?_⟩
  · intro i hi
    by_cases h0 : i = 0
    · subst h0; rw [if_pos rfl]; simp only [Nat.cast_zero, add_zero]; rw [g7, b3.2.1 7 (by decide), h7]
    · have hne : Gb + (i : ℤ) ≠ Gb := by
        intro e; have : (i : ℤ) = 0 := by linarith
        omega
      rw [if_neg h0, g8 _ hne]
      exact b2 i hi
  · exact fr_trans (fr_mono b3 (by decide) (by decide) (fun _ h => h))
      ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun y _ => by rw [g6], fun z hz => g8 z (by rintro rfl; exact hz ⟨le_rfl, by push_cast; omega⟩), g9⟩

lemma ef_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (d : ℕ) (lD kk vb Sb P52 : ℤ)
    (hf vf sf : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 255) (hh : s.halted = false)
    (h3 : s.core.ptrs 3 = d) (h17 : s.core.ptrs 17 = lD) (h48 : s.core.ptrs 48 = kk)
    (h51 : s.core.ptrs 51 = vb) (h15 : s.core.ptrs 15 = Sb) (h18 : s.core.ptrs 18 = 0)
    (h52 : s.core.ptrs 52 = P52) (h19 : s.core.regs 19 = 0)
    (hH : ∀ r : ℕ, r < d → s.core.mem (P52 + r * d) = hf r)
    (hV : ∀ r : ℕ, r < d → s.core.mem (vb + r) = vf r)
    (hS : ∀ r : ℕ, r < d → s.core.mem (Sb - lD - r) = sf r) :
    ∃ u, u ≤ d * 15 + 3 ∧ (run Q s detTape u).core.pc = off + 273 ∧ (run Q s detTape u).halted = false ∧
      (run Q s detTape u).work = s.work + u ∧
      (run Q s detTape u).core.regs 19 =
        ∑ r ∈ range d, (if lD + r ≤ kk then hf r * vf r * sf r else 0) ∧
      (run Q s detTape u).core.regs 0 = 1 ∧ (run Q s detTape u).core.ptrs 5 = 0 ∧
      Fr {5, 11, 18, 19, 52} {0, 19, 20, 21} (fun _ => False) s (run Q s detTape u) := by
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 18 = t ∧ s'.core.ptrs 52 = P52 + t * d ∧
    s'.core.regs 19 = ∑ r ∈ range t, (if lD + r ≤ kk then hf r * vf r * sf r else 0) ∧
    Fr {11, 18, 19, 52} {0, 19, 20, 21} (fun _ => False) s s'
  have hst : ∀ t s', t < d → Inv t s' → s'.core.pc = off + 255 → s'.halted = false →
      ∃ u, u ≤ 15 ∧ (run Q s' detTape u).core.pc = off + 255 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3, i4⟩ hpc' hh'
    have e3 : s'.core.ptrs 3 = d := by rw [i4.1 3 (by decide), h3]
    have e17 : s'.core.ptrs 17 = lD := by rw [i4.1 17 (by decide), h17]
    have e48 : s'.core.ptrs 48 = kk := by rw [i4.1 48 (by decide), h48]
    have e51 : s'.core.ptrs 51 = vb := by rw [i4.1 51 (by decide), h51]
    have e15 : s'.core.ptrs 15 = Sb := by rw [i4.1 15 (by decide), h15]
    have em : s'.core.mem = s.core.mem := funext fun z => i4.2.2.1 z (fun h => h)
    have hb0 : s'.core.ptrs 18 < s'.core.ptrs 3 := by rw [i1, e3]; exact_mod_cast ht
    by_cases hc : lD + t ≤ kk
    · obtain ⟨g1, g2, _, g4, _, g6, g7, _, g9, _, _, g12, g13, g14, g15, _⟩ :=
        ef_fix Q off q hE (hf t) (vf t) (sf t) s' hpc' hh'
          (by rw [i2, em]; exact hH t ht) (by rw [e51, i1, em]; exact hV t ht)
          (by rw [e15, e17, i1, em]; exact hS t ht) hb0 (by rw [e17, i1, e48]; exact hc)
      refine ⟨15, le_rfl, g1, g2, g15, by rw [g4, i1]; push_cast; ring,
        by rw [g6, i2, e3]; push_cast; ring, by rw [g9, i3, sum_range_succ, if_pos hc], ?_⟩
      exact fr_trans i4 ⟨fun y hy => g7 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
          (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun y hy => g12 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
          (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun z _ => by rw [g13], g14⟩
    · push Not at hc
      obtain ⟨g1, g2, g3, _, g5, g6, g7, _, g9, g10, g11, g12, _⟩ :=
        ef_free Q off q hE s' hpc' hh' hb0 (by rw [e17, i1, e48]; exact hc)
      refine ⟨9, by omega, g1, g2, g12, by rw [g3, i1]; push_cast; ring,
        by rw [g5, i2, e3]; push_cast; ring,
        by rw [g7, i3, sum_range_succ, if_neg (by push Not; exact hc), add_zero], ?_⟩
      exact fr_trans i4 ⟨fun y hy => g6 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
          (by rintro rfl; exact hy (by decide)),
        fun y hy => g9 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun z _ => by rw [g10], g11⟩
  obtain ⟨u, hu, a1, a2, a3, b1, _, b3, b4⟩ :=
    loop_inv (Q := Q) Inv d 15 hst d 0 s (by omega)
      ⟨by rw [h18]; rfl, by rw [h52]; simp, by rw [h19]; simp, fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
    ef_exit Q off q hE _ a1 a2 (by rw [b4.1 3 (by decide), h3, b1])
  refine ⟨u + 3, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g9, a3]; ring, by rw [g6 19 (by decide), b3], g5, g3, ?_⟩
  exact fr_trans (fr_mono b4 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => g4 y (by rintro rfl; exact hy (by decide)),
      fun y hy => g6 y (by rintro rfl; exact hy (by decide)), fun z _ => by rw [g7], g8⟩

lemma c0_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (K1 : ℕ) (Fb Cb : ℤ)
    (hFC : Fb + K1 ≤ Cb) (s : State) (hpc : s.core.pc = off + 273) (hh : s.halted = false)
    (h39 : s.core.ptrs 39 = K1) (h40 : s.core.ptrs 40 = Fb) (h41 : s.core.ptrs 41 = Cb)
    (h5 : s.core.ptrs 5 = 0) (h0 : s.core.regs 0 = 1)
    (hF : ∀ i : ℕ, i < K1 → s.core.mem (Fb + i) = (i.factorial : ℝ)) :
    ∃ u, u ≤ K1 * 9 + 3 ∧ (run Q s detTape u).core.pc = off + 284 ∧ (run Q s detTape u).halted = false ∧
      (run Q s detTape u).work = s.work + u ∧
      (∀ i : ℕ, i < K1 → (run Q s detTape u).core.mem (Cb + i) = s.core.regs 19 ^ i / (i.factorial : ℝ)) ∧
      (run Q s detTape u).core.ptrs 18 = 0 ∧
      (run Q s detTape u).core.ptrs 52 = s.core.ptrs 24 + s.core.ptrs 20 ∧
      Fr {5, 11, 18, 52} {0, 1} (fun z => Cb ≤ z ∧ z < Cb + K1) s (run Q s detTape u) := by
  let Wm : ℤ → Prop := fun z => Cb ≤ z ∧ z < Cb + K1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 5 = t ∧ s'.core.regs 0 = s.core.regs 19 ^ t ∧
    (∀ i : ℕ, i < t → s'.core.mem (Cb + i) = s.core.regs 19 ^ i / (i.factorial : ℝ)) ∧
    Fr {5, 11} {0, 1} Wm s s'
  have hst : ∀ t s', t < K1 → Inv t s' → s'.core.pc = off + 273 → s'.halted = false →
      ∃ u, u ≤ 9 ∧ (run Q s' detTape u).core.pc = off + 273 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3, i4⟩ hpc' hh'
    have hfr : s'.core.mem (s'.core.ptrs 40 + s'.core.ptrs 5) = (t.factorial : ℝ) := by
      rw [i4.1 40 (by decide), h40, i1, i4.2.2.1 _ (by
        rintro ⟨h1, _⟩; have : (t : ℤ) < K1 := by exact_mod_cast ht
        linarith)]
      exact hF t ht
    obtain ⟨g1, g2, g3, _, g5, g6, _, g8, g9, g10, g11, g12, _⟩ :=
      c0_step Q off q hE _ s' hpc' hh' hfr (by rw [i1, i4.1 39 (by decide), h39]; exact_mod_cast ht)
    rw [i4.1 41 (by decide), h41, i1] at g9 g10
    refine ⟨9, le_rfl, g1, g2, g12, by rw [g3, i1]; push_cast; ring,
      by rw [g6, i2, i4.2.1 19 (by decide), pow_succ], ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge i t with h | h
      · have hne : Cb + (i : ℤ) ≠ Cb + (t : ℤ) := by
          intro e; have : (i : ℤ) = t := by linarith
          omega
        rw [g10 _ hne]; exact i3 i h
      · have : i = t := by omega
        subst this; rw [g9, i2]
    · exact fr_trans i4 ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun y hy => g8 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun z hz => g10 z (by rintro rfl; exact hz ⟨by linarith, by push_cast; linarith⟩), g11⟩
  obtain ⟨u, hu, a1, a2, a3, b1, _, b3, b4⟩ :=
    loop_inv (Q := Q) Inv K1 9 hst K1 0 s (by omega)
      ⟨by rw [h5]; rfl, by rw [h0]; simp, fun i h => absurd h (Nat.not_lt_zero _), fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ :=
    c0_exit Q off q hE _ a1 a2 (by rw [b4.1 39 (by decide), h39, b1])
  set s1 := run Q (run Q s detTape u) detTape 1 with hs1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, _⟩ := c0d Q off q hE s1 g1 g2
  refine ⟨u + 1 + 2, by omega, ?_⟩
  rw [run_add, run_add, ← hs1]
  refine ⟨k1, k2, by rw [k9, g7, a3]; ring, fun i hi => by rw [k7, g5]; exact b3 i hi, k3,
    by rw [k4, g3, b4.1 24 (by decide), b4.1 20 (by decide)], ?_⟩
  exact fr_trans (fr_mono b4 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => by rw [k5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)), g3],
      fun y _ => by rw [k6, g4], fun z _ => by rw [k7, g5], by rw [k8, g6]⟩

end DetANN.Supplement.Thm32

-- ===== T32_EvalB =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP Finset

lemma et_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (m : ℕ) (Fb Cb Tb : ℤ)
    (a : ℝ) (Cf : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 300) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h40 : s.core.ptrs 40 = Fb)
    (h41 : s.core.ptrs 41 = Cb) (h42 : s.core.ptrs 42 = Tb) (h53 : s.core.ptrs 53 = m)
    (h5 : s.core.ptrs 5 = 0) (h54 : s.core.ptrs 54 = 0) (h55 : s.core.ptrs 55 = m + 1)
    (h22 : s.core.regs 22 = a) (h23 : s.core.regs 23 = 0) (h24 : s.core.regs 24 = 1)
    (hF : ∀ i : ℕ, i ≤ m → s.core.mem (Fb + i) = (i.factorial : ℝ))
    (hC : ∀ i : ℕ, i ≤ m → s.core.mem (Cb + i) = Cf i) :
    ∃ u, u ≤ (m + 1) * 14 + 5 ∧ (run Q s detTape u).core.pc = off + 293 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (run Q s detTape u).core.mem (Tb + m) = ∑ i ∈ range (m + 1), coshTerm a Cf m i ∧
      (run Q s detTape u).core.ptrs 53 = m + 1 ∧
      Fr {5, 11, 53, 54} {0, 1, 23, 24} (fun z => z = Tb + m) s (run Q s detTape u) := by
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 5 = t ∧ s'.core.ptrs 54 = (t % 2 : ℕ) ∧
    s'.core.regs 24 = a ^ t ∧ s'.core.regs 23 = ∑ i ∈ range t, coshTerm a Cf m i ∧
    Fr {5, 11, 54} {0, 1, 23, 24} (fun _ => False) s s'
  have hst : ∀ t s', t < m + 1 → Inv t s' → s'.core.pc = off + 300 → s'.halted = false →
      ∃ u, u ≤ 14 ∧ (run Q s' detTape u).core.pc = off + 300 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3, i4, i5⟩ hpc' hh'
    have em : s'.core.mem = s.core.mem := funext fun z => i5.2.2.1 z (fun h => h)
    have hb0 : s'.core.ptrs 5 < s'.core.ptrs 55 := by
      rw [i1, i5.1 55 (by decide), h55]; exact_mod_cast ht
    have e22 : s'.core.regs 22 = a := by rw [i5.2.1 22 (by decide), h22]
    by_cases hp : t % 2 = 0
    · have hfr0 : s'.core.mem (s'.core.ptrs 40 + s'.core.ptrs 5) = (t.factorial : ℝ) := by
        rw [i5.1 40 (by decide), h40, i1, em]; exact hF t (by omega)
      have hfr1 : s'.core.mem (s'.core.ptrs 41 + s'.core.ptrs 53 - s'.core.ptrs 5) = Cf (m - t) := by
        rw [i5.1 41 (by decide), h41, i5.1 53 (by decide), h53, i1, em,
          show Cb + (m : ℤ) - t = Cb + ((m - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ m)]; ring]
        exact hC _ (by omega)
      obtain ⟨g1, g2, g3, _, g5, g6, _, _, g9, g10, g11, g12, g13, g14, _⟩ :=
        et_even Q off q hE _ _ s' hpc' hh' hfr0 hfr1 hb0
          (by rw [i2, i5.1 0 (by decide), h0, hp]; simp)
      refine ⟨14, le_rfl, g1, g2, g14, by rw [g3, i1]; push_cast; ring, ?_, ?_, ?_, ?_⟩
      · rw [g5, i5.1 1 (by decide), h1, i2, hp]; push_cast; omega
      · rw [g10, i3, e22, pow_succ]
      · rw [g9, i4, i3, sum_range_succ]; unfold coshTerm; rw [if_pos hp]
      · exact fr_trans i5 ⟨fun y hy => g6 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
            (by rintro rfl; exact hy (by decide)),
          fun y hy => g11 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
            (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
          fun z _ => by rw [g12], g13⟩
    · have hp1 : t % 2 = 1 := by omega
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
        et_odd Q off q hE s' hpc' hh' hb0 (by rw [i2, i5.1 0 (by decide), h0, hp1]; simp)
      refine ⟨7, by omega, g1, g2, g10, by rw [g3, i1]; push_cast; ring, ?_, ?_, ?_, ?_⟩
      · rw [g4, i5.1 1 (by decide), h1, i2, hp1]; push_cast; omega
      · rw [g6, i3, e22, pow_succ]
      · rw [g7 23 (by decide), i4, sum_range_succ]; unfold coshTerm; rw [if_neg hp]; ring
      · exact fr_trans i5 ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
          fun y hy => g7 y (by rintro rfl; exact hy (by decide)), fun z _ => by rw [g8], g9⟩
  obtain ⟨u, hu, a1, a2, a3, b1, _, _, b4, b5⟩ :=
    loop_inv (Q := Q) Inv (m + 1) 14 hst (m + 1) 0 s (by omega)
      ⟨by rw [h5]; rfl, by rw [h54]; rfl, by rw [h24]; simp, by rw [h23]; simp, fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
    et_exit Q off q hE _ a1 a2 (by rw [b5.1 55 (by decide), h55, b1]; push_cast; rfl)
  rw [b5.1 42 (by decide), b5.1 53 (by decide), h42, h53] at g7 g8
  refine ⟨u + 5, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g10, a3]; ring, by rw [g7, b4], by rw [g4, b5.1 53 (by decide), h53], ?_⟩
  exact fr_trans (fr_mono b5 (by decide) (by decide) (fun _ h => h.elim))
    ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun y _ => by rw [g6], fun z hz => g8 z hz, g9⟩

lemma em_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (K1 : ℕ) (Fb Cb Tb : ℤ)
    (hCT : Cb + K1 ≤ Tb) (hFC : Fb + K1 ≤ Cb) (a : ℝ) (Cf : ℕ → ℝ) (s : State)
    (hpc : s.core.pc = off + 293) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h39 : s.core.ptrs 39 = K1)
    (h40 : s.core.ptrs 40 = Fb) (h41 : s.core.ptrs 41 = Cb) (h42 : s.core.ptrs 42 = Tb)
    (h53 : s.core.ptrs 53 = 0) (h22 : s.core.regs 22 = a)
    (hF : ∀ i : ℕ, i < K1 → s.core.mem (Fb + i) = (i.factorial : ℝ))
    (hC : ∀ i : ℕ, i < K1 → s.core.mem (Cb + i) = Cf i) :
    ∃ u, u ≤ K1 * ((K1 + 1) * 14 + 12) + 2 ∧ (run Q s detTape u).core.pc = off + 320 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (∀ m : ℕ, m < K1 → (run Q s detTape u).core.mem (Tb + m) = ∑ i ∈ range (m + 1), coshTerm a Cf m i) ∧
      (run Q s detTape u).core.ptrs 5 = 0 ∧
      Fr {5, 11, 53, 54, 55} {0, 1, 23, 24} (fun z => Tb ≤ z ∧ z < Tb + K1) s (run Q s detTape u) := by
  let Wm : ℤ → Prop := fun z => Tb ≤ z ∧ z < Tb + K1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 53 = t ∧
    (∀ m : ℕ, m < t → s'.core.mem (Tb + m) = ∑ i ∈ range (m + 1), coshTerm a Cf m i) ∧
    Fr {5, 11, 53, 54, 55} {0, 1, 23, 24} Wm s s'
  have hst : ∀ t s', t < K1 → Inv t s' → s'.core.pc = off + 293 → s'.halted = false →
      ∃ u, u ≤ (K1 + 1) * 14 + 12 ∧ (run Q s' detTape u).core.pc = off + 293 ∧
        (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
      em_head Q off q hE s' hpc' hh' (by rw [i1, i3.1 39 (by decide), h39]; exact_mod_cast ht)
    set s1 := run Q s' detTape 7 with hs1
    have hK : (t : ℤ) < K1 := by exact_mod_cast ht
    have mF : ∀ i : ℕ, i ≤ t → s1.core.mem (Fb + i) = (i.factorial : ℝ) := by
      intro i hi
      have : (i : ℤ) ≤ t := by exact_mod_cast hi
      rw [g10, i3.2.2.1 _ (by rintro ⟨h, _⟩; linarith)]; exact hF i (by omega)
    have mC : ∀ i : ℕ, i ≤ t → s1.core.mem (Cb + i) = Cf i := by
      intro i hi
      have : (i : ℤ) ≤ t := by exact_mod_cast hi
      rw [g10, i3.2.2.1 _ (by rintro ⟨h, _⟩; linarith)]; exact hC i (by omega)
    obtain ⟨u2, hu2, e1, e2, e3, e4, e5, e6⟩ :=
      et_loop Q off q hE t Fb Cb Tb a Cf s1 g1 g2
        (by rw [g6 0 (by decide) (by decide) (by decide), i3.1 0 (by decide), h0])
        (by rw [g6 1 (by decide) (by decide) (by decide), i3.1 1 (by decide), h1])
        (by rw [g6 40 (by decide) (by decide) (by decide), i3.1 40 (by decide), h40])
        (by rw [g6 41 (by decide) (by decide) (by decide), i3.1 41 (by decide), h41])
        (by rw [g6 42 (by decide) (by decide) (by decide), i3.1 42 (by decide), h42])
        (by rw [g6 53 (by decide) (by decide) (by decide), i1]) g3 g4 (by rw [g5, i1])
        (by rw [g9 22 (by decide) (by decide), i3.2.1 22 (by decide), h22]) g7 g8 mF mC
    refine ⟨7 + u2, by omega, ?_⟩
    rw [run_add, ← hs1]
    refine ⟨e1, e2, by rw [e3, g12]; ring, e5, ?_, ?_⟩
    · intro m hm
      rcases Nat.lt_or_ge m t with h | h
      · have hne : Tb + (m : ℤ) ≠ Tb + (t : ℤ) := by
          intro e; have : (m : ℤ) = t := by linarith
          omega
        rw [e6.2.2.1 _ hne, g10]; exact i2 m h
      · have : m = t := by omega
        subst this; exact e4
    · have f1 : Fr {5, 11, 53, 54, 55} {0, 1, 23, 24} Wm s' s1 :=
        ⟨fun y hy => g6 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
            (by rintro rfl; exact hy (by decide)),
          fun y hy => g9 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
          fun z _ => by rw [g10], g11⟩
      exact fr_trans (fr_trans i3 f1) (fr_mono e6 (by decide) (by decide)
        (fun z hz => by rw [hz]; exact ⟨by linarith, by linarith⟩))
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv K1 ((K1 + 1) * 14 + 12) hst K1 0 s (by omega)
      ⟨by rw [h53]; rfl, fun m h => absurd h (Nat.not_lt_zero _), fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
    em_exit Q off q hE _ a1 a2 (by rw [b3.1 39 (by decide), h39, b1])
  refine ⟨u + 2, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g8, a3]; ring, fun m hm => by rw [g6]; exact b2 m hm, g3, ?_⟩
  exact fr_trans b3 ⟨fun y hy => g4 y (by rintro rfl; exact hy (by decide)),
    fun y _ => by rw [g5], fun z _ => by rw [g6], g7⟩

lemma cp_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (K1 : ℕ) (Cb Tb : ℤ)
    (hCT : Cb + K1 ≤ Tb) (Tf : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 320) (hh : s.halted = false)
    (h39 : s.core.ptrs 39 = K1) (h41 : s.core.ptrs 41 = Cb) (h42 : s.core.ptrs 42 = Tb)
    (h5 : s.core.ptrs 5 = 0) (hT : ∀ i : ℕ, i < K1 → s.core.mem (Tb + i) = Tf i) :
    ∃ u, u ≤ K1 * 7 + 4 ∧ (run Q s detTape u).core.pc = off + 284 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (∀ i : ℕ, i < K1 → (run Q s detTape u).core.mem (Cb + i) = Tf i) ∧
      (run Q s detTape u).core.ptrs 18 = s.core.ptrs 18 + 1 ∧
      (run Q s detTape u).core.ptrs 52 = s.core.ptrs 52 + s.core.ptrs 3 ∧
      Fr {5, 11, 18, 52} {0} (fun z => Cb ≤ z ∧ z < Cb + K1) s (run Q s detTape u) := by
  let Wm : ℤ → Prop := fun z => Cb ≤ z ∧ z < Cb + K1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 5 = t ∧
    (∀ i : ℕ, i < t → s'.core.mem (Cb + i) = Tf i) ∧ Fr {5, 11} {0} Wm s s'
  have hst : ∀ t s', t < K1 → Inv t s' → s'.core.pc = off + 320 → s'.halted = false →
      ∃ u, u ≤ 7 ∧ (run Q s' detTape u).core.pc = off + 320 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have hK : (t : ℤ) < K1 := by exact_mod_cast ht
    have hfr : s'.core.mem (s'.core.ptrs 42 + s'.core.ptrs 5) = Tf t := by
      rw [i3.1 42 (by decide), h42, i1, i3.2.2.1 _ (by rintro ⟨_, h⟩; linarith)]; exact hT t ht
    obtain ⟨g1, g2, g3, _, g5, _, g7, g8, g9, g10, g11, _⟩ :=
      cp_step Q off q hE _ s' hpc' hh' hfr (by rw [i1, i3.1 39 (by decide), h39]; exact_mod_cast ht)
    rw [i3.1 41 (by decide), h41, i1] at g8 g9
    refine ⟨7, le_rfl, g1, g2, g11, by rw [g3, i1]; push_cast; ring, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge i t with h | h
      · have hne : Cb + (i : ℤ) ≠ Cb + (t : ℤ) := by
          intro e; have : (i : ℤ) = t := by linarith
          omega
        rw [g9 _ hne]; exact i2 i h
      · have : i = t := by omega
        subst this; rw [g8]
    · exact fr_trans i3 ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun y hy => g7 y (by rintro rfl; exact hy (by decide)),
        fun z hz => g9 z (by rintro rfl; exact hz ⟨by linarith, by push_cast; linarith⟩), g10⟩
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv K1 7 hst K1 0 s (by omega)
      ⟨by rw [h5]; rfl, fun i h => absurd h (Nat.not_lt_zero _), fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
    cp_exit Q off q hE _ a1 a2 (by rw [b3.1 39 (by decide), h39, b1])
  refine ⟨u + 4, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g9, a3]; ring, fun i hi => by rw [g7]; exact b2 i hi,
    by rw [g3, b3.1 18 (by decide)], by rw [g4, b3.1 52 (by decide), b3.1 3 (by decide)], ?_⟩
  exact fr_trans (fr_mono b3 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun y _ => by rw [g6], fun z _ => by rw [g7], g8⟩

lemma er_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (d K1 : ℕ)
    (Fb Cb Tb lD kk vb P52 : ℤ) (hCT : Cb + K1 ≤ Tb) (hFC : Fb + K1 ≤ Cb) (hf vf : ℕ → ℝ)
    (S : ℕ → PowerSeries ℝ)
    (hSs : ∀ r, r < d → S (r + 1) = S r * coshSeries (if lD + r ≤ kk then 0 else hf r * vf r))
    (s : State) (hpc : s.core.pc = off + 284) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h3 : s.core.ptrs 3 = d)
    (h17 : s.core.ptrs 17 = lD) (h48 : s.core.ptrs 48 = kk) (h51 : s.core.ptrs 51 = vb)
    (h39 : s.core.ptrs 39 = K1) (h40 : s.core.ptrs 40 = Fb) (h41 : s.core.ptrs 41 = Cb)
    (h42 : s.core.ptrs 42 = Tb) (h18 : s.core.ptrs 18 = 0) (h52 : s.core.ptrs 52 = P52)
    (hH : ∀ r : ℕ, r < d → s.core.mem (P52 + r * d) = hf r) (hHr : ∀ r : ℕ, r < d → P52 + r * d < Cb)
    (hV : ∀ r : ℕ, r < d → s.core.mem (vb + r) = vf r) (hVr : ∀ r : ℕ, r < d → vb + r < Cb)
    (hF : ∀ i : ℕ, i < K1 → s.core.mem (Fb + i) = (i.factorial : ℝ))
    (hC0 : ∀ m : ℕ, m < K1 → s.core.mem (Cb + m) = PowerSeries.coeff m (S 0)) :
    ∃ u, u ≤ d * (K1 * ((K1 + 1) * 14 + 12) + K1 * 7 + 15) + 2 ∧ (run Q s detTape u).core.pc = off + 331 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (∀ m : ℕ, m < K1 → (run Q s detTape u).core.mem (Cb + m) = PowerSeries.coeff m (S d)) ∧
      (run Q s detTape u).core.ptrs 56 = 0 ∧
      Fr {5, 11, 18, 19, 52, 53, 54, 55, 56} {0, 1, 21, 22, 23, 24} (fun z => Cb ≤ z ∧ z < Tb + K1) s
        (run Q s detTape u) := by
  let Wm : ℤ → Prop := fun z => Cb ≤ z ∧ z < Tb + K1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 18 = t ∧ s'.core.ptrs 52 = P52 + t * d ∧
    (∀ m : ℕ, m < K1 → s'.core.mem (Cb + m) = PowerSeries.coeff m (S t)) ∧
    Fr {5, 11, 18, 19, 52, 53, 54, 55} {0, 1, 21, 22, 23, 24} Wm s s'
  have hst : ∀ t s', t < d → Inv t s' → s'.core.pc = off + 284 → s'.halted = false →
      ∃ u, u ≤ K1 * ((K1 + 1) * 14 + 12) + K1 * 7 + 15 ∧ (run Q s' detTape u).core.pc = off + 284 ∧
        (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3, i4⟩ hpc' hh'
    have P : ∀ y, y ∉ ({5, 11, 18, 19, 52, 53, 54, 55} : Finset ℕ) → s'.core.ptrs y = s.core.ptrs y := i4.1
    have hb0 : s'.core.ptrs 18 < s'.core.ptrs 3 := by rw [i1, P 3 (by decide), h3]; exact_mod_cast ht
    -- the coefficient `a` of this coordinate
    have hA : ∃ u1, u1 ≤ 9 ∧ (run Q s' detTape u1).core.pc = off + 293 ∧
        (run Q s' detTape u1).halted = false ∧ (run Q s' detTape u1).work = s'.work + u1 ∧
        (run Q s' detTape u1).core.ptrs 53 = 0 ∧
        (run Q s' detTape u1).core.regs 22 = (if lD + t ≤ kk then 0 else hf t * vf t) ∧
        Fr {11, 19, 53} {0, 21, 22} (fun _ => False) s' (run Q s' detTape u1) := by
      by_cases hc : lD + t ≤ kk
      · obtain ⟨g1, g2, _, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
          er_fix Q off q hE s' hpc' hh' hb0 (by rw [P 17 (by decide), h17, i1, P 48 (by decide), h48]; exact hc)
        exact ⟨5, by omega, g1, g2, g10, g4, by rw [g6, if_pos hc],
          ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
            fun y hy => g7 y (by rintro rfl; exact hy (by decide)), fun z _ => by rw [g8], g9⟩⟩
      · push Not at hc
        have ht' : (t : ℤ) < d := by exact_mod_cast ht
        have hH' : s'.core.mem (s'.core.ptrs 52) = hf t := by
          rw [i2, i4.2.2.1 _ (by rintro ⟨h, _⟩; have := hHr t ht; linarith)]; exact hH t ht
        have hV' : s'.core.mem (s'.core.ptrs 51 + s'.core.ptrs 18) = vf t := by
          rw [P 51 (by decide), h51, i1, i4.2.2.1 _ (by rintro ⟨h, _⟩; have := hVr t ht; linarith)]
          exact hV t ht
        obtain ⟨g1, g2, _, _, g5, g6, _, _, g9, g10, g11, g12, g13, _⟩ :=
          er_free Q off q hE _ _ s' hpc' hh' hH' hV' hb0
            (by rw [P 17 (by decide), h17, i1, P 48 (by decide), h48]; exact hc)
        exact ⟨9, le_rfl, g1, g2, g13, g5, by rw [g9, if_neg (by push Not; exact hc)],
          ⟨fun y hy => g6 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
              (by rintro rfl; exact hy (by decide)),
            fun y hy => g10 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
              (by rintro rfl; exact hy (by decide)), fun z _ => by rw [g11], g12⟩⟩
    obtain ⟨u1, hu1, a1, a2, a3, a4, a5, a6⟩ := hA
    set s1 := run Q s' detTape u1 with hs1
    have P1 : ∀ y, y ∉ ({5, 11, 18, 19, 52, 53, 54, 55} : Finset ℕ) → s1.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [a6.1 y (fun e => hy (by simp at e ⊢; omega)), P y hy]
    have M1 : ∀ z, ¬ Wm z → s1.core.mem z = s.core.mem z :=
      fun z hz => by rw [a6.2.2.1 z (fun h => h), i4.2.2.1 z hz]
    -- the cosh multiplication
    obtain ⟨u2, hu2, e1, e2, e3, e4, e5, e6⟩ :=
      em_loop Q off q hE K1 Fb Cb Tb hCT hFC _ (fun m => PowerSeries.coeff m (S t)) s1 a1 a2
        (by rw [P1 0 (by decide), h0]) (by rw [P1 1 (by decide), h1]) (by rw [P1 39 (by decide), h39])
        (by rw [P1 40 (by decide), h40]) (by rw [P1 41 (by decide), h41]) (by rw [P1 42 (by decide), h42]) a4 a5
        (fun i hi => by
          have : (i : ℤ) < K1 := by exact_mod_cast hi
          rw [M1 _ (by rintro ⟨h, _⟩; linarith)]; exact hF i hi)
        (fun i hi => by rw [a6.2.2.1 _ (fun h => h)]; exact i3 i hi)
    set s2 := run Q s1 detTape u2 with hs2
    have P2 : ∀ y, y ∉ ({5, 11, 18, 19, 52, 53, 54, 55} : Finset ℕ) → s2.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [e6.1 y (fun e => hy (by simp at e ⊢; omega)), P1 y hy]
    obtain ⟨u3, hu3, c1, c2, c3, c4, c5, c6, c7⟩ :=
      cp_loop Q off q hE K1 Cb Tb hCT (fun m => PowerSeries.coeff m (S (t + 1))) s2 e1 e2
        (by rw [P2 39 (by decide), h39]) (by rw [P2 41 (by decide), h41]) (by rw [P2 42 (by decide), h42]) e5
        (fun m hm => by
          rw [e4 m hm, hSs t ht]
          exact cosh_step _ _ _ m (fun i hi => rfl))
    refine ⟨u1 + u2 + u3, by omega, ?_⟩
    rw [run_add, run_add, ← hs1, ← hs2]
    refine ⟨c1, c2, by rw [c3, e3, a3]; ring, ?_, ?_, c4, ?_⟩
    · rw [c5, e6.1 18 (by decide), a6.1 18 (by decide), i1]; push_cast; ring
    · rw [c6, e6.1 52 (by decide), a6.1 52 (by decide), i2, e6.1 3 (by decide), a6.1 3 (by decide),
        P 3 (by decide), h3]; push_cast; ring
    · have m1 := fr_mono a6 (Wp' := {5, 11, 18, 19, 52, 53, 54, 55}) (Wr' := {0, 1, 21, 22, 23, 24})
        (Wm' := Wm) (by decide) (by decide) (fun _ h => h.elim)
      have m2 := fr_mono e6 (Wp' := {5, 11, 18, 19, 52, 53, 54, 55}) (Wr' := {0, 1, 21, 22, 23, 24})
        (Wm' := Wm) (by decide) (by decide) (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩)
      have m3 := fr_mono c7 (Wp' := {5, 11, 18, 19, 52, 53, 54, 55}) (Wr' := {0, 1, 21, 22, 23, 24})
        (Wm' := Wm) (by decide) (by decide) (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩)
      exact fr_trans (fr_trans (fr_trans i4 m1) m2) m3
  obtain ⟨u, hu, a1, a2, a3, b1, _, b3, b4⟩ :=
    loop_inv (Q := Q) Inv d (K1 * ((K1 + 1) * 14 + 12) + K1 * 7 + 15) hst d 0 s (by omega)
      ⟨by rw [h18]; rfl, by rw [h52]; simp, hC0, fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ :=
    er_exit Q off q hE _ a1 a2 (by rw [b4.1 3 (by decide), h3, b1])
  set s1 := run Q (run Q s detTape u) detTape 1 with hs1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, _⟩ := erd Q off q hE s1 g1 g2
  refine ⟨u + 1 + 1, by omega, ?_⟩
  rw [run_add, run_add, ← hs1]
  refine ⟨k1, k2, by rw [k8, g7, a3]; ring, fun m hm => by rw [k6, g5]; exact b3 m hm, k3, ?_⟩
  exact fr_trans (fr_mono b4 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => by rw [k4 y (by rintro rfl; exact hy (by decide)), g3],
      fun y _ => by rw [k5, g4], fun z _ => by rw [k6, g5], by rw [k7, g6]⟩

end DetANN.Supplement.Thm32

-- ===== T32_EvalC =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP Finset

lemma ei_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (κ : ℕ) (Fb Cb PNb Eb : ℤ)
    (PN Cf : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 336) (hh : s.halted = false)
    (h40 : s.core.ptrs 40 = Fb) (h41 : s.core.ptrs 41 = Cb) (h43 : s.core.ptrs 43 = PNb)
    (h46 : s.core.ptrs 46 = Eb) (h56 : s.core.ptrs 56 = κ) (h10 : s.core.ptrs 10 = 0)
    (h57 : s.core.ptrs 57 = κ + 1) (h23 : s.core.regs 23 = 0)
    (hF : ∀ i : ℕ, i ≤ 2 * κ → s.core.mem (Fb + i) = (i.factorial : ℝ))
    (hP : ∀ i : ℕ, i ≤ κ → s.core.mem (PNb + i) = PN i)
    (hC : ∀ i : ℕ, i ≤ κ → s.core.mem (Cb + (2 * i : ℕ)) = Cf (2 * i)) :
    ∃ u, u ≤ (κ + 1) * 23 + 8 ∧ (run Q s detTape u).core.pc = off + 331 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (run Q s detTape u).core.mem (Eb + κ) =
        (∑ i ∈ range (κ + 1), momTerm PN Cf κ i) / (κ.factorial : ℝ) ∧
      (run Q s detTape u).core.ptrs 56 = κ + 1 ∧
      Fr {10, 11, 12, 56, 58} {0, 1, 23} (fun z => z = Eb + κ) s (run Q s detTape u) := by
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 10 = t ∧
    s'.core.regs 23 = ∑ i ∈ range t, momTerm PN Cf κ i ∧ Fr {10, 11, 12, 58} {0, 1, 23} (fun _ => False) s s'
  have hst : ∀ t s', t < κ + 1 → Inv t s' → s'.core.pc = off + 336 → s'.halted = false →
      ∃ u, u ≤ 23 ∧ (run Q s' detTape u).core.pc = off + 336 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have em : s'.core.mem = s.core.mem := funext fun z => i3.2.2.1 z (fun h => h)
    have P : ∀ y, y ∉ ({10, 11, 12, 58} : Finset ℕ) → s'.core.ptrs y = s.core.ptrs y := i3.1
    have htk : t ≤ κ := by omega
    obtain ⟨g1, g2, g3, _, _, _, g7, _, _, g10, g11, g12, g13, g14, _⟩ :=
      ei_step Q off q hE (κ.factorial : ℝ) (t.factorial : ℝ) ((κ - t).factorial : ℝ) (PN (κ - t))
        ((2 * t).factorial : ℝ) (Cf (2 * t)) s' hpc' hh'
        (by rw [P 40 (by decide), P 56 (by decide), h40, h56, em]; exact hF κ (by omega))
        (by rw [P 40 (by decide), i1, h40, em]; exact hF t (by omega))
        (by rw [P 40 (by decide), P 56 (by decide), i1, h40, h56, em,
              show Fb + (κ : ℤ) - t = Fb + ((κ - t : ℕ) : ℤ) by push_cast [Nat.cast_sub htk]; ring]
            exact hF _ (by omega))
        (by rw [P 43 (by decide), P 56 (by decide), i1, h43, h56, em,
              show PNb + (κ : ℤ) - t = PNb + ((κ - t : ℕ) : ℤ) by push_cast [Nat.cast_sub htk]; ring]
            exact hP _ (by omega))
        (by rw [P 40 (by decide), i1, h40, em, show Fb + 2 * (t : ℤ) = Fb + ((2 * t : ℕ) : ℤ) by push_cast; ring]
            exact hF _ (by omega))
        (by rw [P 41 (by decide), i1, h41, em, show Cb + 2 * (t : ℤ) = Cb + ((2 * t : ℕ) : ℤ) by push_cast; ring]
            exact hC t htk)
        (by rw [i1, P 57 (by decide), h57]; exact_mod_cast ht)
    refine ⟨23, le_rfl, g1, g2, g14, by rw [g3, i1]; push_cast; ring, by rw [g10, i2, sum_range_succ]; rfl, ?_⟩
    exact fr_trans i3 ⟨fun y hy => g7 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
        (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun y hy => g11 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
        (by rintro rfl; exact hy (by decide)),
      fun z _ => by rw [g12], g13⟩
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv (κ + 1) 23 hst (κ + 1) 0 s (by omega)
      ⟨by rw [h10]; rfl, by rw [h23]; simp, fr_refl _ _ _ _⟩ hpc hh
  have em : (run Q s detTape u).core.mem = s.core.mem := funext fun z => b3.2.2.1 z (fun h => h)
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
    ei_exit Q off q hE (κ.factorial : ℝ) _ a1 a2
      (by rw [b3.1 40 (by decide), b3.1 56 (by decide), h40, h56, em]; exact hF κ (by omega))
      (by rw [b3.1 57 (by decide), h57, b1]; push_cast; rfl)
  rw [b3.1 46 (by decide), b3.1 56 (by decide), h46, h56] at g9 g10
  refine ⟨u + 8, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g12, a3]; ring, by rw [g9, b2], by rw [g4, b3.1 56 (by decide), h56], ?_⟩
  exact fr_trans (fr_mono b3 (by decide) (by decide) (fun _ h => h.elim))
    ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun y hy => g8 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun z hz => g10 z hz, g11⟩

lemma ek_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (K1 P1 : ℕ)
    (hKP : 2 * P1 ≤ K1 + 1) (Fb Cb PNb Eb : ℤ) (hrg : Fb + K1 ≤ Cb ∧ Cb + K1 ≤ PNb ∧ PNb + P1 ≤ Eb)
    (nv : ℝ) (S : PowerSeries ℝ) (s : State) (hpc : s.core.pc = off + 331) (hh : s.halted = false)
    (h37 : s.core.ptrs 37 = P1) (h40 : s.core.ptrs 40 = Fb) (h41 : s.core.ptrs 41 = Cb)
    (h43 : s.core.ptrs 43 = PNb) (h46 : s.core.ptrs 46 = Eb) (h56 : s.core.ptrs 56 = 0)
    (hF : ∀ i : ℕ, i < K1 → s.core.mem (Fb + i) = (i.factorial : ℝ))
    (hP : ∀ i : ℕ, i < P1 → s.core.mem (PNb + i) = (-nv) ^ i)
    (hC : ∀ i : ℕ, i < K1 → s.core.mem (Cb + i) = PowerSeries.coeff i S) :
    ∃ u, u ≤ P1 * (P1 * 23 + 13) + 2 ∧ (run Q s detTape u).core.pc = off + 367 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (∀ κ : ℕ, κ < P1 → (run Q s detTape u).core.mem (Eb + κ) = PowerSeries.coeff κ (xSeries nv S)) ∧
      (run Q s detTape u).core.ptrs 53 = 0 ∧
      Fr {10, 11, 12, 53, 56, 57, 58} {0, 1, 23} (fun z => Eb ≤ z ∧ z < Eb + P1) s (run Q s detTape u) := by
  obtain ⟨r1, r2, r3⟩ := hrg
  let Wm : ℤ → Prop := fun z => Eb ≤ z ∧ z < Eb + P1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 56 = t ∧
    (∀ κ : ℕ, κ < t → s'.core.mem (Eb + κ) = PowerSeries.coeff κ (xSeries nv S)) ∧
    Fr {10, 11, 12, 56, 57, 58} {0, 1, 23} Wm s s'
  have hst : ∀ t s', t < P1 → Inv t s' → s'.core.pc = off + 331 → s'.halted = false →
      ∃ u, u ≤ P1 * 23 + 13 ∧ (run Q s' detTape u).core.pc = off + 331 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have P : ∀ y, y ∉ ({10, 11, 12, 56, 57, 58} : Finset ℕ) → s'.core.ptrs y = s.core.ptrs y := i3.1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
      ek_head Q off q hE s' hpc' hh' (by rw [i1, P 37 (by decide), h37]; exact_mod_cast ht)
    set s1 := run Q s' detTape 5 with hs1
    have M : ∀ z, ¬ Wm z → s1.core.mem z = s.core.mem z := fun z hz => by rw [g8, i3.2.2.1 z hz]
    have P1' : ∀ y, y ∉ ({10, 11, 12, 56, 57, 58} : Finset ℕ) → s1.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [g5 y (fun e => hy (by simp [e])) (fun e => hy (by simp [e])), P y hy]
    have ht' : (t : ℤ) < P1 := by exact_mod_cast ht
    obtain ⟨u2, hu2, e1, e2, e3, e4, e5, e6⟩ :=
      ei_loop Q off q hE t Fb Cb PNb Eb (fun j => (-nv) ^ j) (fun i => PowerSeries.coeff i S) s1 g1 g2
        (by rw [P1' 40 (by decide), h40]) (by rw [P1' 41 (by decide), h41]) (by rw [P1' 43 (by decide), h43])
        (by rw [P1' 46 (by decide), h46]) (by rw [g5 56 (by decide) (by decide), i1]) g3
        (by rw [g4, i1]) g6
        (fun i hi => by
          have : (i : ℤ) < K1 := by have : i < K1 := by omega
                                    exact_mod_cast this
          rw [M _ (by rintro ⟨h, _⟩; linarith)]; exact hF i (by omega))
        (fun i hi => by
          have : (i : ℤ) < P1 := by have : i < P1 := by omega
                                    exact_mod_cast this
          rw [M _ (by rintro ⟨h, _⟩; linarith)]; exact hP i (by omega))
        (fun i hi => by
          have hlt : 2 * i < K1 := by omega
          have : ((2 * i : ℕ) : ℤ) < K1 := by exact_mod_cast hlt
          rw [M _ (by rintro ⟨h, _⟩; linarith)]; exact hC _ hlt)
    refine ⟨5 + u2, by
        have : (t + 1) * 23 ≤ P1 * 23 := Nat.mul_le_mul_right _ ht
        omega, ?_⟩
    rw [run_add, ← hs1]
    refine ⟨e1, e2, by rw [e3, g10]; ring, e5, ?_, ?_⟩
    · intro κ hκ
      rcases Nat.lt_or_ge κ t with h | h
      · have hne : Eb + (κ : ℤ) ≠ Eb + (t : ℤ) := by
          intro e; have : (κ : ℤ) = t := by linarith
          omega
        rw [e6.2.2.1 _ hne, g8]; exact i2 κ h
      · have : κ = t := by omega
        subst this
        rw [e4]
        exact mom_step nv S _ _ κ (fun j _ => rfl) (fun i _ => rfl)
    · have f1 : Fr {10, 11, 12, 56, 57, 58} {0, 1, 23} Wm s' s1 :=
        ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
          fun y hy => g7 y (by rintro rfl; exact hy (by decide)), fun z _ => by rw [g8], g9⟩
      exact fr_trans (fr_trans i3 f1) (fr_mono e6 (by decide) (by decide)
        (fun z hz => by rw [hz]; exact ⟨by linarith, by linarith⟩))
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv P1 (P1 * 23 + 13) hst P1 0 s (by omega)
      ⟨by rw [h56]; rfl, fun κ h => absurd h (Nat.not_lt_zero _), fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
    ek_exit Q off q hE _ a1 a2 (by rw [b3.1 37 (by decide), h37, b1])
  refine ⟨u + 2, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g8, a3]; ring, fun κ hκ => by rw [g6]; exact b2 κ hκ, g3, ?_⟩
  exact fr_trans (fr_mono b3 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => g4 y (by rintro rfl; exact hy (by decide)), fun y _ => by rw [g5], fun z _ => by rw [g6], g7⟩

lemma gt_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (m : ℕ) (Gb TGb Eb : ℤ)
    (G Ef : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 372) (hh : s.halted = false)
    (h44 : s.core.ptrs 44 = Gb) (h45 : s.core.ptrs 45 = TGb) (h46 : s.core.ptrs 46 = Eb)
    (h53 : s.core.ptrs 53 = m) (h5 : s.core.ptrs 5 = 0) (h55 : s.core.ptrs 55 = m + 1)
    (h23 : s.core.regs 23 = 0)
    (hG : ∀ i : ℕ, i ≤ m → s.core.mem (Gb + i) = G i) (hEf : ∀ i : ℕ, i ≤ m → s.core.mem (Eb + i) = Ef i) :
    ∃ u, u ≤ (m + 1) * 10 + 5 ∧ (run Q s detTape u).core.pc = off + 367 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (run Q s detTape u).core.mem (TGb + m) = ∑ i ∈ range (m + 1), G i * Ef (m - i) ∧
      (run Q s detTape u).core.ptrs 53 = m + 1 ∧
      Fr {5, 11, 12, 53} {0, 1, 23} (fun z => z = TGb + m) s (run Q s detTape u) := by
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 5 = t ∧
    s'.core.regs 23 = ∑ i ∈ range t, G i * Ef (m - i) ∧ Fr {5, 11, 12} {0, 1, 23} (fun _ => False) s s'
  have hst : ∀ t s', t < m + 1 → Inv t s' → s'.core.pc = off + 372 → s'.halted = false →
      ∃ u, u ≤ 10 ∧ (run Q s' detTape u).core.pc = off + 372 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have em : s'.core.mem = s.core.mem := funext fun z => i3.2.2.1 z (fun h => h)
    have P : ∀ y, y ∉ ({5, 11, 12} : Finset ℕ) → s'.core.ptrs y = s.core.ptrs y := i3.1
    obtain ⟨g1, g2, g3, _, _, g6, _, _, g9, g10, g11, g12, g13, _⟩ :=
      gt_step Q off q hE (G t) (Ef (m - t)) s' hpc' hh'
        (by rw [P 44 (by decide), i1, h44, em]; exact hG t (by omega))
        (by rw [P 46 (by decide), P 53 (by decide), i1, h46, h53, em,
              show Eb + (m : ℤ) - t = Eb + ((m - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ m)]; ring]
            exact hEf _ (by omega))
        (by rw [i1, P 55 (by decide), h55]; exact_mod_cast ht)
    refine ⟨10, le_rfl, g1, g2, g13, by rw [g3, i1]; push_cast; ring, by rw [g9, i2, sum_range_succ], ?_⟩
    exact fr_trans i3 ⟨fun y hy => g6 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
        (by rintro rfl; exact hy (by decide)),
      fun y hy => g10 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide))
        (by rintro rfl; exact hy (by decide)),
      fun z _ => by rw [g11], g12⟩
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv (m + 1) 10 hst (m + 1) 0 s (by omega)
      ⟨by rw [h5]; rfl, by rw [h23]; simp, fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
    gt_exit Q off q hE _ a1 a2 (by rw [b3.1 55 (by decide), h55, b1]; push_cast; rfl)
  rw [b3.1 45 (by decide), b3.1 53 (by decide), h45, h53] at g7 g8
  refine ⟨u + 5, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g10, a3]; ring, by rw [g7, b2], by rw [g4, b3.1 53 (by decide), h53], ?_⟩
  exact fr_trans (fr_mono b3 (by decide) (by decide) (fun _ h => h.elim))
    ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun y _ => by rw [g6], fun z hz => g8 z hz, g9⟩

lemma gm_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (P1 : ℕ) (Gb TGb Eb : ℤ)
    (hrg : Gb + P1 ≤ TGb ∧ TGb + P1 ≤ Eb) (A B : PowerSeries ℝ) (s : State) (hpc : s.core.pc = off + 367)
    (hh : s.halted = false) (h37 : s.core.ptrs 37 = P1) (h44 : s.core.ptrs 44 = Gb)
    (h45 : s.core.ptrs 45 = TGb) (h46 : s.core.ptrs 46 = Eb) (h53 : s.core.ptrs 53 = 0)
    (hG : ∀ i : ℕ, i < P1 → s.core.mem (Gb + i) = PowerSeries.coeff i A)
    (hEf : ∀ i : ℕ, i < P1 → s.core.mem (Eb + i) = PowerSeries.coeff i B) :
    ∃ u, u ≤ P1 * (P1 * 10 + 10) + 2 ∧ (run Q s detTape u).core.pc = off + 387 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (∀ m : ℕ, m < P1 → (run Q s detTape u).core.mem (TGb + m) = PowerSeries.coeff m (A * B)) ∧
      (run Q s detTape u).core.ptrs 5 = 0 ∧
      Fr {5, 11, 12, 53, 55} {0, 1, 23} (fun z => TGb ≤ z ∧ z < TGb + P1) s (run Q s detTape u) := by
  obtain ⟨r1, r2⟩ := hrg
  let Wm : ℤ → Prop := fun z => TGb ≤ z ∧ z < TGb + P1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 53 = t ∧
    (∀ m : ℕ, m < t → s'.core.mem (TGb + m) = PowerSeries.coeff m (A * B)) ∧
    Fr {5, 11, 12, 53, 55} {0, 1, 23} Wm s s'
  have hst : ∀ t s', t < P1 → Inv t s' → s'.core.pc = off + 367 → s'.halted = false →
      ∃ u, u ≤ P1 * 10 + 10 ∧ (run Q s' detTape u).core.pc = off + 367 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have P : ∀ y, y ∉ ({5, 11, 12, 53, 55} : Finset ℕ) → s'.core.ptrs y = s.core.ptrs y := i3.1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
      gm_head Q off q hE s' hpc' hh' (by rw [i1, P 37 (by decide), h37]; exact_mod_cast ht)
    set s1 := run Q s' detTape 5 with hs1
    have M : ∀ z, ¬ Wm z → s1.core.mem z = s.core.mem z := fun z hz => by rw [g8, i3.2.2.1 z hz]
    have P1' : ∀ y, y ∉ ({5, 11, 12, 53, 55} : Finset ℕ) → s1.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [g5 y (fun e => hy (by simp [e])) (fun e => hy (by simp [e])), P y hy]
    have ht' : (t : ℤ) < P1 := by exact_mod_cast ht
    obtain ⟨u2, hu2, e1, e2, e3, e4, e5, e6⟩ :=
      gt_loop Q off q hE t Gb TGb Eb (fun i => PowerSeries.coeff i A) (fun i => PowerSeries.coeff i B) s1 g1 g2
        (by rw [P1' 44 (by decide), h44]) (by rw [P1' 45 (by decide), h45]) (by rw [P1' 46 (by decide), h46])
        (by rw [g5 53 (by decide) (by decide), i1]) g3 (by rw [g4, i1]) g6
        (fun i hi => by
          have : (i : ℤ) ≤ t := by exact_mod_cast hi
          rw [M _ (by rintro ⟨h, _⟩; linarith)]; exact hG i (by omega))
        (fun i hi => by
          have : (i : ℤ) ≤ t := by exact_mod_cast hi
          rw [M _ (by rintro ⟨_, h⟩; linarith)]; exact hEf i (by omega))
    refine ⟨5 + u2, by
        have : (t + 1) * 10 ≤ P1 * 10 := Nat.mul_le_mul_right _ ht
        omega, ?_⟩
    rw [run_add, ← hs1]
    refine ⟨e1, e2, by rw [e3, g10]; ring, e5, ?_, ?_⟩
    · intro m hm
      rcases Nat.lt_or_ge m t with h | h
      · have hne : TGb + (m : ℤ) ≠ TGb + (t : ℤ) := by
          intro e; have : (m : ℤ) = t := by linarith
          omega
        rw [e6.2.2.1 _ hne, g8]; exact i2 m h
      · have : m = t := by omega
        subst this
        rw [e4]
        exact prod_step A B _ _ m (fun i _ => rfl) (fun i _ => rfl)
    · have f1 : Fr {5, 11, 12, 53, 55} {0, 1, 23} Wm s' s1 :=
        ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
          fun y hy => g7 y (by rintro rfl; exact hy (by decide)), fun z _ => by rw [g8], g9⟩
      exact fr_trans (fr_trans i3 f1) (fr_mono e6 (by decide) (by decide)
        (fun z hz => by rw [hz]; exact ⟨by linarith, by linarith⟩))
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv P1 (P1 * 10 + 10) hst P1 0 s (by omega)
      ⟨by rw [h53]; rfl, fun m h => absurd h (Nat.not_lt_zero _), fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
    gm_exit Q off q hE _ a1 a2 (by rw [b3.1 37 (by decide), h37, b1])
  refine ⟨u + 2, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g8, a3]; ring, fun m hm => by rw [g6]; exact b2 m hm, g3, ?_⟩
  exact fr_trans b3 ⟨fun y hy => g4 y (by rintro rfl; exact hy (by decide)), fun y _ => by rw [g5],
    fun z _ => by rw [g6], g7⟩

lemma gc_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (P1 : ℕ) (Gb TGb : ℤ)
    (hGT : Gb + P1 ≤ TGb) (Tf : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 387) (hh : s.halted = false)
    (h37 : s.core.ptrs 37 = P1) (h44 : s.core.ptrs 44 = Gb) (h45 : s.core.ptrs 45 = TGb)
    (h5 : s.core.ptrs 5 = 0) (hT : ∀ i : ℕ, i < P1 → s.core.mem (TGb + i) = Tf i) :
    ∃ u, u ≤ P1 * 7 + 4 ∧ (run Q s detTape u).core.pc = off + 251 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (∀ i : ℕ, i < P1 → (run Q s detTape u).core.mem (Gb + i) = Tf i) ∧
      (run Q s detTape u).core.ptrs 16 = s.core.ptrs 16 + 1 ∧
      (run Q s detTape u).core.ptrs 17 = s.core.ptrs 17 + s.core.ptrs 3 ∧
      Fr {5, 11, 16, 17} {0} (fun z => Gb ≤ z ∧ z < Gb + P1) s (run Q s detTape u) := by
  let Wm : ℤ → Prop := fun z => Gb ≤ z ∧ z < Gb + P1
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 5 = t ∧
    (∀ i : ℕ, i < t → s'.core.mem (Gb + i) = Tf i) ∧ Fr {5, 11} {0} Wm s s'
  have hst : ∀ t s', t < P1 → Inv t s' → s'.core.pc = off + 387 → s'.halted = false →
      ∃ u, u ≤ 7 ∧ (run Q s' detTape u).core.pc = off + 387 ∧ (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have hK : (t : ℤ) < P1 := by exact_mod_cast ht
    have hfr : s'.core.mem (s'.core.ptrs 45 + s'.core.ptrs 5) = Tf t := by
      rw [i3.1 45 (by decide), h45, i1, i3.2.2.1 _ (by rintro ⟨_, h⟩; linarith)]; exact hT t ht
    obtain ⟨g1, g2, g3, _, g5, _, g7, g8, g9, g10, g11, _⟩ :=
      gc_step Q off q hE _ s' hpc' hh' hfr (by rw [i1, i3.1 37 (by decide), h37]; exact_mod_cast ht)
    rw [i3.1 44 (by decide), h44, i1] at g8 g9
    refine ⟨7, le_rfl, g1, g2, g11, by rw [g3, i1]; push_cast; ring, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge i t with h | h
      · have hne : Gb + (i : ℤ) ≠ Gb + (t : ℤ) := by
          intro e; have : (i : ℤ) = t := by linarith
          omega
        rw [g9 _ hne]; exact i2 i h
      · have : i = t := by omega
        subst this; rw [g8]
    · exact fr_trans i3 ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
        fun y hy => g7 y (by rintro rfl; exact hy (by decide)),
        fun z hz => g9 z (by rintro rfl; exact hz ⟨by linarith, by push_cast; linarith⟩), g10⟩
  obtain ⟨u, hu, a1, a2, a3, b1, b2, b3⟩ :=
    loop_inv (Q := Q) Inv P1 7 hst P1 0 s (by omega)
      ⟨by rw [h5]; rfl, fun i h => absurd h (Nat.not_lt_zero _), fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
    gc_exit Q off q hE _ a1 a2 (by rw [b3.1 37 (by decide), h37, b1])
  refine ⟨u + 4, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g9, a3]; ring, fun i hi => by rw [g7]; exact b2 i hi,
    by rw [g3, b3.1 16 (by decide)], by rw [g4, b3.1 17 (by decide), b3.1 3 (by decide)], ?_⟩
  exact fr_trans (fr_mono b3 (by decide) (by decide) (fun _ h => h))
    ⟨fun y hy => g5 y (by rintro rfl; exact hy (by decide)) (by rintro rfl; exact hy (by decide)),
      fun y _ => by rw [g6], fun z _ => by rw [g7], g8⟩

end DetANN.Supplement.Thm32

-- ===== T32_EvalD =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP Finset

lemma idx_ltE {r j D : ℕ} (hr : r < D) (hj : j < D) : r * D + j < D * D := by
  have : (r + 1) * D ≤ D * D := Nat.mul_le_mul_right _ hr
  nlinarith

lemma mask_iff {L d kk : ℕ} (ℓ : Fin L) (r : Fin d) :
    prefixMask L d (kk + 1) ℓ r = true ↔ (((ℓ : ℕ) * d : ℕ) : ℤ) + (r : ℕ) ≤ kk := by
  unfold prefixMask
  rw [decide_eq_true_iff]
  constructor
  · intro h; have : (ℓ : ℕ) * d + r ≤ kk := by omega
    exact_mod_cast this
  · intro h; have : (ℓ : ℕ) * d + r ≤ kk := by exact_mod_cast h
    omega

lemma fixed_eq {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (u : Fin L → Fin d → Bool) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (ℓ : Fin L) (kk : ℕ) (hf vf sf : ℕ → ℝ)
    (hhf : ∀ r (hr : r < d), hf r = h j ⟨r, hr⟩) (hvf : ∀ r (hr : r < d), vf r = v ⟨r, hr⟩)
    (hsf : ∀ r (hr : r < d), sf r = signOf (u ℓ ⟨r, hr⟩)) :
    ∑ r ∈ range d, (if (((ℓ : ℕ) * d : ℕ) : ℤ) + r ≤ kk then hf r * vf r * sf r else 0) =
      fixedPart h (prefixMask L d (kk + 1)) u j v ℓ := by
  unfold fixedPart
  rw [← Fin.sum_univ_eq_sum_range (fun r => if (((ℓ : ℕ) * d : ℕ) : ℤ) + r ≤ kk then hf r * vf r * sf r else 0)]
  apply sum_congr rfl
  intro r _
  by_cases hc : (((ℓ : ℕ) * d : ℕ) : ℤ) + (r : ℕ) ≤ kk
  · rw [if_pos hc, if_pos ((mask_iff ℓ r).2 hc), hhf r r.isLt, hvf r r.isLt, hsf r r.isLt]
  · rw [if_neg hc, if_neg (fun e => hc ((mask_iff ℓ r).1 e))]

lemma free_eq {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) (v : EuclideanSpace ℝ (Fin d))
    (ℓ : Fin L) (kk : ℕ) (hf vf : ℕ → ℝ) (hhf : ∀ r (hr : r < d), hf r = h j ⟨r, hr⟩)
    (hvf : ∀ r (hr : r < d), vf r = v ⟨r, hr⟩) (r : ℕ) (hr : r < d) :
    (if (((ℓ : ℕ) * d : ℕ) : ℤ) + r ≤ kk then 0 else hf r * vf r) =
      freeCoeff h (prefixMask L d (kk + 1)) j v ℓ ⟨r, hr⟩ := by
  unfold freeCoeff
  by_cases hc : (((ℓ : ℕ) * d : ℕ) : ℤ) + r ≤ kk
  · rw [if_pos hc, if_pos ((mask_iff ℓ ⟨r, hr⟩).2 hc)]
  · rw [if_neg hc, if_neg (fun e => hc ((mask_iff ℓ ⟨r, hr⟩).1 e)), hhf r hr, hvf r hr]

lemma ySer_succ {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ u : Fin L → Fin d → Bool) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (ℓ : Fin L) (r : ℕ) (hr : r < d) :
    ySer h μ u j v ℓ (r + 1) = ySer h μ u j v ℓ r * coshSeries (freeCoeff h μ j v ℓ ⟨r, hr⟩) := by
  unfold ySer; rw [prod_lt_succ _ r hr]; ring

lemma ySer_zero {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ u : Fin L → Fin d → Bool) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (ℓ : Fin L) :
    ySer h μ u j v ℓ 0 = expSeries (fixedPart h μ u j v ℓ) := by
  unfold ySer; rw [prod_lt_zero, mul_one]

lemma gSer_succ {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ u : Fin L → Fin d → Bool) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (t : ℕ) (ht : t < L) :
    gSer h μ u j v (t + 1) = gSer h μ u j v t * xSeries (‖v‖ ^ 2) (ySer h μ u j v ⟨t, ht⟩ d) := by
  unfold gSer; rw [prod_lt_succ _ t ht]

lemma gSer_zero {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ u : Fin L → Fin d → Bool) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d)) : gSer (L := L) h μ u j v 0 = 1 := by
  unfold gSer; rw [prod_lt_zero]

/-- The step bound of one repetition. -/
def BL (d K1 P1 : ℕ) : ℕ :=
  4 + (d * 15 + 3) + (K1 * 9 + 3) + (d * (K1 * ((K1 + 1) * 14 + 12) + K1 * 7 + 15) + 2) +
    (P1 * (P1 * 23 + 13) + 2) + (P1 * (P1 * 10 + 10) + 2) + (P1 * 7 + 4)

lemma el_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (k L kk K1 P1 : ℕ)
    (hKP : K1 + 1 = 2 * P1) (hP1 : 1 ≤ P1) (ξ : Fin L → Fin (2 ^ k) → Bool) (j : Fin (2 ^ k))
    (v : EuclideanSpace ℝ (Fin (2 ^ k))) (nv : ℝ) (hnv : nv = ‖v‖ ^ 2)
    (Hb vb Fb Cb Tb PNb Gb TGb Eb : ℤ)
    (hb : Cb = Fb + K1 ∧ Tb = Cb + K1 ∧ PNb = Tb + K1 ∧ Gb = PNb + P1 ∧ TGb = Gb + P1 ∧ Eb = TGb + P1)
    (hHv : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ vb) (hvt : vb + ((2 ^ k : ℕ) : ℤ) ≤ Fb) (hH0 : 0 ≤ Hb)
    (s : State) (hpc : s.core.pc = off + 251) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h3 : s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ))
    (h14 : s.core.ptrs 14 = L) (h15 : s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1) (h24 : s.core.ptrs 24 = Hb)
    (h20 : s.core.ptrs 20 = (j : ℕ)) (h37 : s.core.ptrs 37 = P1) (h39 : s.core.ptrs 39 = K1)
    (h40 : s.core.ptrs 40 = Fb) (h41 : s.core.ptrs 41 = Cb) (h42 : s.core.ptrs 42 = Tb)
    (h43 : s.core.ptrs 43 = PNb) (h44 : s.core.ptrs 44 = Gb) (h45 : s.core.ptrs 45 = TGb)
    (h46 : s.core.ptrs 46 = Eb) (h48 : s.core.ptrs 48 = kk) (h51 : s.core.ptrs 51 = vb)
    (h16 : s.core.ptrs 16 = 0) (h17 : s.core.ptrs 17 = 0)
    (hcol : ∀ r j : Fin (2 ^ k), s.core.mem (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r)
    (hv : ∀ c : Fin (2 ^ k), s.core.mem (vb + (c : ℕ)) = v c)
    (hF : ∀ i : ℕ, i < K1 → s.core.mem (Fb + i) = (i.factorial : ℝ))
    (hS : SignsAt s.core.mem L k ξ)
    (hPN : ∀ i : ℕ, i < P1 → s.core.mem (PNb + i) = (-nv) ^ i)
    (hG0 : ∀ i : ℕ, i < P1 → s.core.mem (Gb + i) = if i = 0 then 1 else 0) :
    ∃ u, u ≤ L * BL (2 ^ k) K1 P1 + 1 ∧ (run Q s detTape u).core.pc = off + 397 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (∀ m : ℕ, m < P1 → (run Q s detTape u).core.mem (Gb + m) =
        PowerSeries.coeff m (gSer (sylvester k) (prefixMask L (2 ^ k) (kk + 1)) ξ j v L)) ∧
      Fr {5, 10, 11, 12, 16, 17, 18, 19, 52, 53, 54, 55, 56, 57, 58} {0, 1, 19, 20, 21, 22, 23, 24}
        (fun z => (Cb ≤ z ∧ z < PNb) ∨ (Gb ≤ z ∧ z < Eb + P1)) s (run Q s detTape u) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  set μ := prefixMask L (2 ^ k) (kk + 1) with hμ
  let Wp : Finset ℕ := {5, 10, 11, 12, 16, 17, 18, 19, 52, 53, 54, 55, 56, 57, 58}
  let Wr : Finset ℕ := {0, 1, 19, 20, 21, 22, 23, 24}
  let Wm : ℤ → Prop := fun z => (Cb ≤ z ∧ z < PNb) ∨ (Gb ≤ z ∧ z < Eb + P1)
  have hd0 : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  have hdd : (0 : ℤ) ≤ ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by positivity
  -- the fixed data lies outside `Wm`
  have nW_col : ∀ r j : Fin (2 ^ k), ¬ Wm (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) := by
    intro r j'
    have : (((r : ℕ) * 2 ^ k + j' : ℕ) : ℤ) < ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by
      exact_mod_cast idx_ltE r.isLt j'.isLt
    intro hw; rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have nW_v : ∀ c : ℕ, c < 2 ^ k → ¬ Wm (vb + c) := by
    intro c hc hw
    have : (c : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast hc
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have nW_F : ∀ i : ℕ, i < K1 → ¬ Wm (Fb + i) := by
    intro i hi hw
    have : (i : ℤ) < K1 := by exact_mod_cast hi
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have nW_P : ∀ i : ℕ, i < P1 → ¬ Wm (PNb + i) := by
    intro i hi hw
    have : (i : ℤ) < P1 := by exact_mod_cast hi
    rcases hw with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
  have nW_neg : ∀ z : ℤ, z < 0 → ¬ Wm z := by
    intro z hz hw
    have : (0 : ℤ) ≤ Fb := by omega
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  -- the invariant
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 16 = t ∧ s'.core.ptrs 17 = ((t * 2 ^ k : ℕ) : ℤ) ∧
    (∀ m : ℕ, m < P1 → s'.core.mem (Gb + m) = PowerSeries.coeff m (gSer (sylvester k) μ ξ j v t)) ∧
    Fr Wp Wr Wm s s'
  have hst : ∀ t s', t < L → Inv t s' → s'.core.pc = off + 251 → s'.halted = false →
      ∃ u, u ≤ BL (2 ^ k) K1 P1 ∧ (run Q s' detTape u).core.pc = off + 251 ∧
        (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3, i4⟩ hpc' hh'
    have P : ∀ y, y ∉ Wp → s'.core.ptrs y = s.core.ptrs y := i4.1
    have R : ∀ y, y ∉ Wr → s'.core.regs y = s.core.regs y := i4.2.1
    have M : ∀ z, ¬ Wm z → s'.core.mem z = s.core.mem z := i4.2.2.1
    set ℓ : Fin L := ⟨t, ht⟩ with hℓ
    -- 1. head
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _⟩ :=
      el_head Q off q hE s' hpc' hh' (by rw [i1, P 14 (by decide), h14]; exact_mod_cast ht)
    set s1 := run Q s' detTape 4 with hs1
    have P1' : ∀ y, y ∉ Wp → s1.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [g5 y (fun e => hy (by simp [Wp, e])) (fun e => hy (by simp [Wp, e])), P y hy]
    have M1 : ∀ z, ¬ Wm z → s1.core.mem z = s.core.mem z := fun z hz => by rw [g8, M z hz]
    -- 2. the fixed part
    set hf : ℕ → ℝ := fun r => if hr : r < 2 ^ k then sylvester k j ⟨r, hr⟩ else 0 with hhf
    set vf : ℕ → ℝ := fun r => if hr : r < 2 ^ k then v ⟨r, hr⟩ else 0 with hvf
    set sf : ℕ → ℝ := fun r => if hr : r < 2 ^ k then signOf (ξ ℓ ⟨r, hr⟩) else 0 with hsf
    have eH : ∀ r : ℕ, r < 2 ^ k → s1.core.mem (Hb + (j : ℕ) + r * ((2 ^ k : ℕ) : ℤ)) = hf r := by
      intro r hr
      rw [show Hb + (j : ℕ) + (r : ℤ) * ((2 ^ k : ℕ) : ℤ) = Hb + (((⟨r, hr⟩ : Fin (2 ^ k)) : ℕ) * 2 ^ k + j : ℕ) by
        push_cast; ring, M1 _ (nW_col _ _), hcol]
      simp [hhf, hr]
    have eV : ∀ r : ℕ, r < 2 ^ k → s1.core.mem (vb + r) = vf r := by
      intro r hr
      rw [M1 _ (nW_v r hr)]
      have := hv ⟨r, hr⟩; simp only at this; rw [this]; simp [hvf, hr]
    have eS : ∀ r : ℕ, r < 2 ^ k →
        s1.core.mem (-((2 ^ k : ℕ) : ℤ) - 1 - ((t * 2 ^ k : ℕ) : ℤ) - r) = sf r := by
      intro r hr
      have hneg : -((2 ^ k : ℕ) : ℤ) - 1 - ((t * 2 ^ k : ℕ) : ℤ) - r < 0 := by
        have : (0 : ℤ) ≤ ((t * 2 ^ k : ℕ) : ℤ) := by positivity
        omega
      rw [M1 _ (nW_neg _ hneg)]
      have := hS ℓ ⟨r, hr⟩
      rw [show -((2 ^ k : ℕ) : ℤ) - 1 - ((t * 2 ^ k : ℕ) : ℤ) - r =
        -(2 ^ k : ℤ) - 1 - (((ℓ : ℕ) : ℤ) * 2 ^ k + ((⟨r, hr⟩ : Fin (2 ^ k)) : ℕ)) by
          simp only [hℓ]; push_cast; ring, this]
      simp [hsf, hr]
    obtain ⟨u2, hu2, c1, c2, c3, c4, c5, c6, c7⟩ :=
      ef_loop Q off q hE (2 ^ k) (((t * 2 ^ k : ℕ) : ℤ)) kk vb (-((2 ^ k : ℕ) : ℤ) - 1) (Hb + (j : ℕ))
        hf vf sf s1 g1 g2 (by rw [P1' 3 (by decide), h3]) (by rw [g5 17 (by decide) (by decide), i2])
        (by rw [P1' 48 (by decide), h48]) (by rw [P1' 51 (by decide), h51])
        (by rw [P1' 15 (by decide), h15]) g3 (by rw [g4, P 24 (by decide), P 20 (by decide), h24, h20]) g6
        (fun r hr => by rw [← eH r hr])
        eV eS
    set s2 := run Q s1 detTape u2 with hs2
    have eF : s2.core.regs 19 = fixedPart (sylvester k) μ ξ j v ℓ := by
      rw [c4]
      exact fixed_eq (sylvester k) ξ j v ℓ kk hf vf sf (fun r hr => by simp [hhf, hr])
        (fun r hr => by simp [hvf, hr]) (fun r hr => by simp [hsf, hr])
    have P2' : ∀ y, y ∉ Wp → s2.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [c7.1 y (fun e => hy (by simp [Wp] at e ⊢; omega)), P1' y hy]
    have M2 : ∀ z, ¬ Wm z → s2.core.mem z = s.core.mem z :=
      fun z hz => by rw [c7.2.2.1 z (fun h => h), M1 z hz]
    -- 3. the exponential coefficients
    obtain ⟨u3, hu3, d1, d2, d3, d4, d5, d6, d7⟩ :=
      c0_loop Q off q hE K1 Fb Cb (by omega) s2 c1 c2 (by rw [P2' 39 (by decide), h39])
        (by rw [P2' 40 (by decide), h40]) (by rw [P2' 41 (by decide), h41]) c6 c5
        (fun i hi => by rw [M2 _ (nW_F i hi)]; exact hF i hi)
    set s3 := run Q s2 detTape u3 with hs3
    have P3' : ∀ y, y ∉ Wp → s3.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [d7.1 y (fun e => hy (by simp [Wp] at e ⊢; omega)), P2' y hy]
    have M3 : ∀ z, ¬ Wm z → s3.core.mem z = s.core.mem z := fun z hz => by
      rw [d7.2.2.1 z (fun hw => hz (Or.inl ⟨hw.1, by omega⟩)), M2 z hz]
    -- 4. the coordinates
    obtain ⟨u4, hu4, e1, e2, e3, e4, e5, e6⟩ :=
      er_loop Q off q hE (2 ^ k) K1 Fb Cb Tb (((t * 2 ^ k : ℕ) : ℤ)) kk vb (Hb + (j : ℕ)) (by omega)
        (by omega) hf vf (fun r => ySer (sylvester k) μ ξ j v ℓ r)
        (fun r hr => by
          rw [ySer_succ _ _ _ _ _ ℓ r hr, ← free_eq (sylvester k) j v ℓ kk hf vf
            (fun r hr => by simp [hhf, hr]) (fun r hr => by simp [hvf, hr]) r hr])
        s3 d1 d2 (by rw [P3' 0 (by decide), h0]) (by rw [P3' 1 (by decide), h1])
        (by rw [P3' 3 (by decide), h3]) (by rw [d7.1 17 (by decide), c7.1 17 (by decide),
          g5 17 (by decide) (by decide), i2]) (by rw [P3' 48 (by decide), h48])
        (by rw [P3' 51 (by decide), h51]) (by rw [P3' 39 (by decide), h39]) (by rw [P3' 40 (by decide), h40])
        (by rw [P3' 41 (by decide), h41]) (by rw [P3' 42 (by decide), h42]) d5
        (by rw [d6, P2' 24 (by decide), h24, c7.1 20 (by decide), g5 20 (by decide) (by decide), P 20 (by decide),
          h20])
        (fun r hr => by
          rw [M3 _ (by
            rw [show Hb + (j : ℕ) + (r : ℤ) * ((2 ^ k : ℕ) : ℤ) = Hb + (((⟨r, hr⟩ : Fin (2 ^ k)) : ℕ) * 2 ^ k + j : ℕ) by
              push_cast; ring]; exact nW_col _ _), ← M1 _ (by
            rw [show Hb + (j : ℕ) + (r : ℤ) * ((2 ^ k : ℕ) : ℤ) = Hb + (((⟨r, hr⟩ : Fin (2 ^ k)) : ℕ) * 2 ^ k + j : ℕ) by
              push_cast; ring]; exact nW_col _ _)]
          exact eH r hr)
        (fun r hr => by
          have : (((⟨r, hr⟩ : Fin (2 ^ k)) : ℕ) * 2 ^ k + j : ℕ) < 2 ^ k * 2 ^ k := idx_ltE hr j.isLt
          have h' : ((r * 2 ^ k + j : ℕ) : ℤ) < ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by exact_mod_cast this
          have e : Hb + (j : ℕ) + (r : ℤ) * ((2 ^ k : ℕ) : ℤ) = Hb + ((r * 2 ^ k + j : ℕ) : ℤ) := by push_cast; ring
          rw [e]; omega)
        (fun r hr => by rw [M3 _ (nW_v r hr), ← M1 _ (nW_v r hr)]; exact eV r hr)
        (fun r hr => by have : (r : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast hr
                        omega)
        (fun i hi => by rw [M3 _ (nW_F i hi)]; exact hF i hi)
        (fun m hm => by
          rw [d4 m hm, ySer_zero, coeff_exp, ← eF])
    set s4 := run Q s3 detTape u4 with hs4
    have P4' : ∀ y, y ∉ Wp → s4.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [e6.1 y (fun e => hy (by simp [Wp] at e ⊢; omega)), P3' y hy]
    have M4 : ∀ z, ¬ Wm z → s4.core.mem z = s.core.mem z := fun z hz => by
      rw [e6.2.2.1 z (fun hw => hz (Or.inl ⟨hw.1, by omega⟩)), M3 z hz]
    -- 5. the moments
    obtain ⟨u5, hu5, f1, f2, f3, f4, f5, f6⟩ :=
      ek_loop Q off q hE K1 P1 (by omega) Fb Cb PNb Eb ⟨by omega, by omega, by omega⟩ nv
        (ySer (sylvester k) μ ξ j v ℓ (2 ^ k)) s4 e1 e2 (by rw [P4' 37 (by decide), h37])
        (by rw [P4' 40 (by decide), h40]) (by rw [P4' 41 (by decide), h41]) (by rw [P4' 43 (by decide), h43])
        (by rw [P4' 46 (by decide), h46]) e5
        (fun i hi => by rw [M4 _ (nW_F i hi)]; exact hF i hi)
        (fun i hi => by rw [M4 _ (nW_P i hi)]; exact hPN i hi) e4
    set s5 := run Q s4 detTape u5 with hs5
    have P5' : ∀ y, y ∉ Wp → s5.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [f6.1 y (fun e => hy (by simp [Wp] at e ⊢; omega)), P4' y hy]
    -- the product so far is still in `G`
    have hGs5 : ∀ m : ℕ, m < P1 → s5.core.mem (Gb + m) = PowerSeries.coeff m (gSer (sylvester k) μ ξ j v t) := by
      intro m hm
      have hm' : (m : ℤ) < P1 := by exact_mod_cast hm
      rw [f6.2.2.1 _ (by rintro ⟨h, _⟩; omega), e6.2.2.1 _ (by rintro ⟨_, h⟩; omega),
        d7.2.2.1 _ (by rintro ⟨_, h⟩; omega), c7.2.2.1 _ (fun h => h), g8]
      exact i3 m hm
    -- 6. one more factor
    obtain ⟨u6, hu6, k1, k2, k3, k4, k5, k6⟩ :=
      gm_loop Q off q hE P1 Gb TGb Eb ⟨by omega, by omega⟩ (gSer (sylvester k) μ ξ j v t)
        (xSeries nv (ySer (sylvester k) μ ξ j v ℓ (2 ^ k))) s5 f1 f2 (by rw [P5' 37 (by decide), h37])
        (by rw [P5' 44 (by decide), h44]) (by rw [P5' 45 (by decide), h45]) (by rw [P5' 46 (by decide), h46]) f5
        hGs5 f4
    set s6 := run Q s5 detTape u6 with hs6
    have P6' : ∀ y, y ∉ Wp → s6.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [k6.1 y (fun e => hy (by simp [Wp] at e ⊢; omega)), P5' y hy]
    -- 7. the copy
    obtain ⟨u7, hu7, l1, l2, l3, l4, l5, l6, l7⟩ :=
      gc_loop Q off q hE P1 Gb TGb (by omega)
        (fun m => PowerSeries.coeff m (gSer (sylvester k) μ ξ j v (t + 1))) s6 k1 k2
        (by rw [P6' 37 (by decide), h37]) (by rw [P6' 44 (by decide), h44]) (by rw [P6' 45 (by decide), h45]) k5
        (fun m hm => by rw [k4 m hm, gSer_succ _ _ _ _ _ t ht, hnv])
    refine ⟨4 + u2 + u3 + u4 + u5 + u6 + u7, by unfold BL; omega, ?_⟩
    have e : run Q s' detTape (4 + u2 + u3 + u4 + u5 + u6 + u7) = run Q s6 detTape u7 := by
      rw [run_add, run_add, run_add, run_add, run_add, run_add, ← hs1, ← hs2, ← hs3, ← hs4, ← hs5, ← hs6]
    rw [e]
    refine ⟨l1, l2, by rw [l3, k3, f3, e3, d3, c3, g10]; ring, ?_, ?_, l4, ?_⟩
    · rw [l5, k6.1 16 (by decide), f6.1 16 (by decide), e6.1 16 (by decide), d7.1 16 (by decide),
        c7.1 16 (by decide), g5 16 (by decide) (by decide), i1]; push_cast; ring
    · rw [l6, k6.1 17 (by decide), f6.1 17 (by decide), e6.1 17 (by decide), d7.1 17 (by decide),
        c7.1 17 (by decide), g5 17 (by decide) (by decide), i2, P6' 3 (by decide), h3]; push_cast; ring
    · have f1' : Fr Wp Wr Wm s' s1 :=
        ⟨fun y hy => g5 y (fun e => hy (by simp [Wp, e])) (fun e => hy (by simp [Wp, e])),
          fun y hy => g7 y (fun e => hy (by simp [Wr, e])), fun z _ => by rw [g8], g9⟩
      have m2 := fr_mono c7 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide) (fun _ h => h.elim)
      have m3 := fr_mono d7 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide)
        (fun z hz => Or.inl ⟨hz.1, by omega⟩)
      have m4 := fr_mono e6 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide)
        (fun z hz => Or.inl ⟨hz.1, by omega⟩)
      have m5 := fr_mono f6 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide)
        (fun z hz => Or.inr ⟨by omega, by omega⟩)
      have m6 := fr_mono k6 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide)
        (fun z hz => Or.inr ⟨by omega, by omega⟩)
      have m7 := fr_mono l7 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide)
        (fun z hz => Or.inr ⟨by omega, by omega⟩)
      exact fr_trans (fr_trans (fr_trans (fr_trans (fr_trans (fr_trans (fr_trans i4 f1') m2) m3) m4) m5) m6) m7
  obtain ⟨u, hu, a1, a2, a3, c1, _, c3, c4⟩ :=
    loop_inv (Q := Q) Inv L (BL (2 ^ k) K1 P1) hst L 0 s (by omega)
      ⟨by rw [h16]; rfl, by rw [h17]; simp,
        fun m hm => by rw [hG0 m hm, gSer_zero, PowerSeries.coeff_one], fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ :=
    el_exit Q off q hE _ a1 a2 (by rw [c4.1 14 (by decide), h14, c1])
  refine ⟨u + 1, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g7, a3]; ring, fun m hm => by rw [g5]; exact c3 m hm, ?_⟩
  exact fr_trans c4 ⟨fun y _ => by rw [g3], fun y _ => by rw [g4], fun z _ => by rw [g5], g6⟩

end DetANN.Supplement.Thm32

-- ===== T32_EvalE =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP Finset

/-- The step bound of one column. -/
def BJ (d L K1 P1 : ℕ) : ℕ := 2 + (P1 * 5 + 4) + (L * BL d K1 P1 + 1) + 6

lemma ej_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (k L kk p₀ K1 P1 : ℕ)
    (hK1 : K1 = 4 * p₀ + 1) (hP1 : P1 = 2 * p₀ + 1) (τ : ℝ) (ξ : Fin L → Fin (2 ^ k) → Bool)
    (v : EuclideanSpace ℝ (Fin (2 ^ k))) (nv : ℝ) (hnv : nv = ‖v‖ ^ 2)
    (Hb vb Fb Cb Tb PNb Gb TGb Eb : ℤ)
    (hb : Cb = Fb + K1 ∧ Tb = Cb + K1 ∧ PNb = Tb + K1 ∧ Gb = PNb + P1 ∧ TGb = Gb + P1 ∧ Eb = TGb + P1)
    (hHv : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ vb) (hvt : vb + ((2 ^ k : ℕ) : ℤ) ≤ Fb) (hH0 : 0 ≤ Hb)
    (s : State) (hpc : s.core.pc = off + 241) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h3 : s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ))
    (h14 : s.core.ptrs 14 = L) (h15 : s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1) (h24 : s.core.ptrs 24 = Hb)
    (h20 : s.core.ptrs 20 = 0) (h36 : s.core.ptrs 36 = ((2 * p₀ : ℕ) : ℤ)) (h37 : s.core.ptrs 37 = P1)
    (h39 : s.core.ptrs 39 = K1)
    (h40 : s.core.ptrs 40 = Fb) (h41 : s.core.ptrs 41 = Cb) (h42 : s.core.ptrs 42 = Tb)
    (h43 : s.core.ptrs 43 = PNb) (h44 : s.core.ptrs 44 = Gb) (h45 : s.core.ptrs 45 = TGb)
    (h46 : s.core.ptrs 46 = Eb) (h48 : s.core.ptrs 48 = kk) (h51 : s.core.ptrs 51 = vb)
    (h6 : s.core.regs 6 = 0) (h7 : s.core.regs 7 = 1)
    (h18 : s.core.regs 18 = ((L * τ * nv) ^ (2 * p₀))⁻¹ * ((2 * p₀).factorial : ℝ))
    (hcol : ∀ r j : Fin (2 ^ k), s.core.mem (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r)
    (hv : ∀ c : Fin (2 ^ k), s.core.mem (vb + (c : ℕ)) = v c)
    (hF : ∀ i : ℕ, i < K1 → s.core.mem (Fb + i) = (i.factorial : ℝ))
    (hS : SignsAt s.core.mem L k ξ)
    (hPN : ∀ i : ℕ, i < P1 → s.core.mem (PNb + i) = (-nv) ^ i) :
    ∃ u, u ≤ 2 ^ k * BJ (2 ^ k) L K1 P1 + 1 ∧ (run Q s detTape u).core.pc = off + 403 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (run Q s detTape u).core.regs 13 = s.core.regs 13 +
        ∑ j : Fin (2 ^ k), termVJ (sylvester k) τ p₀ (prefixMask L (2 ^ k) (kk + 1)) ξ v j ∧
      Fr {5, 10, 11, 12, 16, 17, 18, 19, 20, 52, 53, 54, 55, 56, 57, 58} {0, 1, 13, 19, 20, 21, 22, 23, 24}
        (fun z => (Cb ≤ z ∧ z < PNb) ∨ (Gb ≤ z ∧ z < Eb + P1)) s (run Q s detTape u) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  let Wp : Finset ℕ := {5, 10, 11, 12, 16, 17, 18, 19, 20, 52, 53, 54, 55, 56, 57, 58}
  let Wr : Finset ℕ := {0, 1, 13, 19, 20, 21, 22, 23, 24}
  let Wm : ℤ → Prop := fun z => (Cb ≤ z ∧ z < PNb) ∨ (Gb ≤ z ∧ z < Eb + P1)
  have hd0 : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  have nW_col : ∀ r j : Fin (2 ^ k), ¬ Wm (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) := by
    intro r j'
    have : (((r : ℕ) * 2 ^ k + j' : ℕ) : ℤ) < ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by
      exact_mod_cast idx_ltE r.isLt j'.isLt
    intro hw; rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have nW_v : ∀ c : ℕ, c < 2 ^ k → ¬ Wm (vb + c) := by
    intro c hc hw
    have : (c : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast hc
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have nW_F : ∀ i : ℕ, i < K1 → ¬ Wm (Fb + i) := by
    intro i hi hw
    have : (i : ℤ) < K1 := by exact_mod_cast hi
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have nW_P : ∀ i : ℕ, i < P1 → ¬ Wm (PNb + i) := by
    intro i hi hw
    have : (i : ℤ) < P1 := by exact_mod_cast hi
    rcases hw with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
  have nW_neg : ∀ z : ℤ, z < 0 → ¬ Wm z := by
    intro z hz hw
    have : (0 : ℤ) ≤ Fb := by omega
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  let T : Fin (2 ^ k) → ℝ := fun j => termVJ (sylvester k) τ p₀ (prefixMask L (2 ^ k) (kk + 1)) ξ v j
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 20 = t ∧
    s'.core.regs 13 = s.core.regs 13 + ∑ j ∈ univ.filter (fun j : Fin (2 ^ k) => (j : ℕ) < t), T j ∧
    Fr Wp Wr Wm s s'
  have hst : ∀ t s', t < 2 ^ k → Inv t s' → s'.core.pc = off + 241 → s'.halted = false →
      ∃ u, u ≤ BJ (2 ^ k) L K1 P1 ∧ (run Q s' detTape u).core.pc = off + 241 ∧
        (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have P : ∀ y, y ∉ Wp → s'.core.ptrs y = s.core.ptrs y := i3.1
    have M : ∀ z, ¬ Wm z → s'.core.mem z = s.core.mem z := i3.2.2.1
    -- 1. head
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
      ej_head Q off q hE s' hpc' hh' (by rw [i1, P 3 (by decide), h3]; exact_mod_cast ht)
    set s1 := run Q s' detTape 2 with hs1
    have P1' : ∀ y, y ∉ Wp → s1.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [g4 y (fun e => hy (by simp [Wp, e])), P y hy]
    have R1 : ∀ y, y ∉ Wr → s1.core.regs y = s.core.regs y := fun y hy => by rw [g5, i3.2.1 y hy]
    -- 2. `G := 1`
    obtain ⟨u2, hu2, c1, c2, c3, c4, c5, c6, c7⟩ :=
      g0_loop Q off q hE P1 (by omega) Gb s1 g1 g2 (by rw [P1' 37 (by decide), h37])
        (by rw [P1' 44 (by decide), h44]) g3 (by rw [R1 6 (by decide), h6]) (by rw [R1 7 (by decide), h7])
    set s2 := run Q s1 detTape u2 with hs2
    have P2' : ∀ y, y ∉ Wp → s2.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [c7.1 y (fun e => hy (by simp [Wp] at e ⊢; omega)), P1' y hy]
    have M2 : ∀ z, ¬ Wm z → s2.core.mem z = s.core.mem z := fun z hz => by
      rw [c7.2.2.1 z (fun hw => hz (Or.inr ⟨hw.1, by omega⟩)), g6, M z hz]
    -- 3. the repetitions
    obtain ⟨u3, hu3, e1, e2, e3, e4, e5⟩ :=
      el_loop Q off q hE k L kk K1 P1 (by omega) (by omega) ξ ⟨t, ht⟩ v nv hnv Hb vb Fb Cb Tb PNb Gb TGb Eb
        ⟨b1, b2, b3, b4, b5, b6⟩ hHv hvt hH0 s2 c1 c2
        (by rw [P2' 0 (by decide), h0]) (by rw [P2' 1 (by decide), h1]) (by rw [P2' 3 (by decide), h3])
        (by rw [P2' 14 (by decide), h14]) (by rw [P2' 15 (by decide), h15]) (by rw [P2' 24 (by decide), h24])
        (by rw [c7.1 20 (by decide), g4 20 (by decide), i1]) (by rw [P2' 37 (by decide), h37])
        (by rw [P2' 39 (by decide), h39]) (by rw [P2' 40 (by decide), h40]) (by rw [P2' 41 (by decide), h41])
        (by rw [P2' 42 (by decide), h42]) (by rw [P2' 43 (by decide), h43]) (by rw [P2' 44 (by decide), h44])
        (by rw [P2' 45 (by decide), h45]) (by rw [P2' 46 (by decide), h46]) (by rw [P2' 48 (by decide), h48])
        (by rw [P2' 51 (by decide), h51]) c5 c6
        (fun r j => by rw [M2 _ (nW_col r j)]; exact hcol r j)
        (fun c => by rw [M2 _ (nW_v c c.isLt)]; exact hv c)
        (fun i hi => by rw [M2 _ (nW_F i hi)]; exact hF i hi)
        (by
          intro ℓ r
          have a1 : (0 : ℤ) ≤ ((ℓ : ℕ) : ℤ) * 2 ^ k + ((r : ℕ) : ℤ) := by positivity
          have a2 : (0 : ℤ) < 2 ^ k := by positivity
          rw [M2 _ (nW_neg _ (by omega))]; exact hS ℓ r)
        (fun i hi => by rw [M2 _ (nW_P i hi)]; exact hPN i hi) c4
    set s3 := run Q s2 detTape u3 with hs3
    have P3' : ∀ y, y ∉ Wp → s3.core.ptrs y = s.core.ptrs y :=
      fun y hy => by rw [e5.1 y (fun e => hy (by simp [Wp] at e ⊢; omega)), P2' y hy]
    have R3 : s3.core.regs 18 = s.core.regs 18 := by
      rw [e5.2.1 18 (by decide), c7.2.1 18 (by decide), g5, i3.2.1 18 (by decide)]
    have R13 : s3.core.regs 13 = s'.core.regs 13 := by
      rw [e5.2.1 13 (by decide), c7.2.1 13 (by decide), g5]
    -- 4. accumulate
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, _⟩ :=
      eld Q off q hE (PowerSeries.coeff (2 * p₀)
        (gSer (sylvester k) (prefixMask L (2 ^ k) (kk + 1)) ξ ⟨t, ht⟩ v L)) s3 e1 e2
        (by rw [P3' 44 (by decide), P3' 36 (by decide), h44, h36]; exact e4 _ (by omega))
    refine ⟨2 + u2 + u3 + 6, by unfold BJ; omega, ?_⟩
    have e : run Q s' detTape (2 + u2 + u3 + 6) = run Q s3 detTape 6 := by
      rw [run_add, run_add, run_add, ← hs1, ← hs2, ← hs3]
    rw [e]
    refine ⟨k1, k2, by rw [k11, e3, c3, g8]; ring, ?_, ?_, ?_⟩
    · rw [k4, e5.1 20 (by decide), c7.1 20 (by decide), g4 20 (by decide), i1]; push_cast; ring
    · rw [k7, R13, i2, R3, h18, sum_lt_succ T t ht, add_assoc]
      congr 2
      show _ = termVJ _ _ _ _ _ _ _
      unfold termVJ; rw [hnv]; ring
    · have f1 : Fr Wp Wr Wm s' s1 :=
        ⟨fun y hy => g4 y (fun e => hy (by simp [Wp, e])), fun y _ => by rw [g5], fun z _ => by rw [g6], g7⟩
      have m2 := fr_mono c7 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide)
        (fun z hz => Or.inr ⟨hz.1, by omega⟩)
      have m3 := fr_mono e5 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide) (fun _ h => h)
      have f4 : Fr Wp Wr Wm s3 (run Q s3 detTape 6) :=
        ⟨fun y hy => k5 y (fun e => hy (by simp [Wp, e])) (fun e => hy (by simp [Wp, e])),
          fun y hy => k8 y (fun e => hy (by simp [Wr, e])) (fun e => hy (by simp [Wr, e])),
          fun z _ => by rw [k9], k10⟩
      exact fr_trans (fr_trans (fr_trans (fr_trans i3 f1) m2) m3) f4
  obtain ⟨u, hu, a1, a2, a3, c1, c2, c3⟩ :=
    loop_inv (Q := Q) Inv (2 ^ k) (BJ (2 ^ k) L K1 P1) hst (2 ^ k) 0 s (by omega)
      ⟨by rw [h20]; rfl, by rw [sum_lt_zero, add_zero], fr_refl _ _ _ _⟩ hpc hh
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ :=
    ej_exit Q off q hE _ a1 a2 (by rw [c3.1 3 (by decide), h3, c1])
  refine ⟨u + 1, by omega, ?_⟩
  rw [run_add]
  refine ⟨g1, g2, by rw [g7, a3]; ring, by rw [g4, c2, sum_lt_all], ?_⟩
  exact fr_trans c3 ⟨fun y _ => by rw [g3], fun y _ => by rw [g4], fun z _ => by rw [g5], g6⟩

lemma nv_eq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ∑ c ∈ range n, (if hc : c < n then v ⟨c, hc⟩ else 0) * (if hc : c < n then v ⟨c, hc⟩ else 0) = ‖v‖ ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun c => (if hc : c < n then v ⟨c, hc⟩ else 0) *
    (if hc : c < n then v ⟨c, hc⟩ else 0)), EuclideanSpace.real_norm_sq_eq]
  apply sum_congr rfl
  intro c _
  simp [c.isLt, sq]

/-- The step bound of one table entry. -/
def VB (d L K1 P1 P2 : ℕ) : ℕ :=
  3 + (d * 7 + 4) + (P1 * 6 + 6) + (P2 * 4 + 6) + (d * BJ d L K1 P1 + 1) + 2

lemma ev_body (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (k L kk p₀ K1 P1 : ℕ)
    (hK1 : K1 = 4 * p₀ + 1) (hP1 : P1 = 2 * p₀ + 1) (τ : ℝ) (ξ : Fin L → Fin (2 ^ k) → Bool)
    (v : EuclideanSpace ℝ (Fin (2 ^ k))) (Hb vb E27 Fb Cb Tb PNb Gb TGb Eb : ℤ)
    (hb : Cb = Fb + K1 ∧ Tb = Cb + K1 ∧ PNb = Tb + K1 ∧ Gb = PNb + P1 ∧ TGb = Gb + P1 ∧ Eb = TGb + P1)
    (hHv : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ vb) (hvt : vb + ((2 ^ k : ℕ) : ℤ) ≤ Fb) (hH0 : 0 ≤ Hb)
    (hvE : vb < E27)
    (s : State) (hpc : s.core.pc = off + 208) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h3 : s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ))
    (h14 : s.core.ptrs 14 = L) (h15 : s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1) (h24 : s.core.ptrs 24 = Hb)
    (h27 : s.core.ptrs 27 = E27)
    (h36 : s.core.ptrs 36 = ((2 * p₀ : ℕ) : ℤ)) (h37 : s.core.ptrs 37 = P1) (h39 : s.core.ptrs 39 = K1)
    (h40 : s.core.ptrs 40 = Fb) (h41 : s.core.ptrs 41 = Cb) (h42 : s.core.ptrs 42 = Tb)
    (h43 : s.core.ptrs 43 = PNb) (h44 : s.core.ptrs 44 = Gb) (h45 : s.core.ptrs 45 = TGb)
    (h46 : s.core.ptrs 46 = Eb) (h48 : s.core.ptrs 48 = kk) (h51 : s.core.ptrs 51 = vb)
    (h5 : s.core.regs 5 = τ) (h6 : s.core.regs 6 = 0) (h7 : s.core.regs 7 = 1)
    (hcol : ∀ r j : Fin (2 ^ k), s.core.mem (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r)
    (hv : ∀ c : Fin (2 ^ k), s.core.mem (vb + (c : ℕ)) = v c)
    (hF : ∀ i : ℕ, i < K1 → s.core.mem (Fb + i) = (i.factorial : ℝ))
    (hS : SignsAt s.core.mem L k ξ) :
    ∃ u, u ≤ VB (2 ^ k) L K1 P1 (2 * p₀) ∧ (run Q s detTape u).core.pc = off + 208 ∧
      (run Q s detTape u).halted = false ∧ (run Q s detTape u).work = s.work + u ∧
      (run Q s detTape u).core.ptrs 51 = vb + ((2 ^ k : ℕ) : ℤ) ∧
      (run Q s detTape u).core.regs 13 = s.core.regs 13 +
        ∑ j : Fin (2 ^ k), termVJ (sylvester k) τ p₀ (prefixMask L (2 ^ k) (kk + 1)) ξ v j ∧
      Fr {5, 10, 11, 12, 16, 17, 18, 19, 20, 31, 51, 52, 53, 54, 55, 56, 57, 58}
        {0, 1, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}
        (fun z => Cb ≤ z ∧ z < Eb + P1) s (run Q s detTape u) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  let Wp : Finset ℕ := {5, 10, 11, 12, 16, 17, 18, 19, 20, 31, 51, 52, 53, 54, 55, 56, 57, 58}
  let Wr : Finset ℕ := {0, 1, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}
  let Wm : ℤ → Prop := fun z => Cb ≤ z ∧ z < Eb + P1
  set vf : ℕ → ℝ := fun c => if hc : c < 2 ^ k then v ⟨c, hc⟩ else 0 with hvf
  have hd0 : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  -- 1. head
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
    ev_head Q off q hE s hpc hh (by rw [h51, h27]; exact hvE)
  set s1 := run Q s detTape 3 with hs1
  -- 2. the squared norm
  obtain ⟨u2, hu2, c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
    n2_loop Q off q hE (2 ^ k) vb vf s1 g1 g2 (by rw [g4 3 (by decide), h3]) (by rw [g4 51 (by decide), h51])
      g3 g5 (fun c hc => by
        rw [g7]; have := hv ⟨c, hc⟩; simp only at this; rw [this]; simp [hvf, hc])
  rw [nv_eq v] at c4 c5
  set s2 := run Q s1 detTape u2 with hs2
  have Q2 : ∀ y, y ∉ ({5, 11, 31} : Finset ℕ) → s2.core.ptrs y = s.core.ptrs y := fun y hy => by
    rw [c8.1 y hy, g4 y (fun e => hy (by simp [e]))]
  have M2 : s2.core.mem = s.core.mem := funext fun z => by rw [c8.2.2.1 z (fun h => h), g7]
  -- 3. the powers of `-‖v‖²`
  obtain ⟨u3, hu3, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
    pn_loop Q off q hE P1 PNb s2 c1 c2 (by rw [Q2 37 (by decide), h37]) (by rw [Q2 43 (by decide), h43]) c7 c6
  set s3 := run Q s2 detTape u3 with hs3
  have Q3 : ∀ y, y ∉ ({5, 11, 31} : Finset ℕ) → s3.core.ptrs y = s.core.ptrs y := fun y hy => by
    rw [d9.1 y (fun e => hy (by simp at e ⊢; omega)), Q2 y hy]
  have M3 : ∀ z, ¬ (PNb ≤ z ∧ z < PNb + P1) → s3.core.mem z = s.core.mem z := fun z hz => by
    rw [d9.2.2.1 z hz, M2]
  -- 4. the prefactor
  have hfv : s3.core.mem (Fb + ((2 * p₀ : ℕ) : ℤ)) = ((2 * p₀).factorial : ℝ) := by
    have : ((2 * p₀ : ℕ) : ℤ) < K1 := by push_cast; omega
    rw [M3 _ (by rintro ⟨h, _⟩; omega)]; exact hF _ (by omega)
  obtain ⟨u4, hu4, e1, e2, e3, e4, e5, e6⟩ :=
    bp_loop Q off q hE (2 * p₀) Fb ((2 * p₀).factorial : ℝ) s3 d1 d2 (by rw [Q3 36 (by decide), h36])
      (by rw [Q3 40 (by decide), h40]) d8 d7 hfv
  set s4 := run Q s3 detTape u4 with hs4
  have Q4 : ∀ y, y ∉ ({5, 11, 20, 31} : Finset ℕ) → s4.core.ptrs y = s.core.ptrs y := fun y hy => by
    rw [e6.1 y (fun e => hy (by simp at e ⊢; omega)), Q3 y (fun e => hy (by simp at e ⊢; omega))]
  have M4 : ∀ z, ¬ (PNb ≤ z ∧ z < PNb + P1) → s4.core.mem z = s.core.mem z := fun z hz => by
    rw [e6.2.2.1 z (fun h => h), M3 z hz]
  have nP : ∀ z, z < Cb → ¬ (PNb ≤ z ∧ z < PNb + P1) := fun z hz h => by omega
  have r18 : s4.core.regs 18 = ((L * τ * ‖v‖ ^ 2) ^ (2 * p₀))⁻¹ * ((2 * p₀).factorial : ℝ) := by
    rw [e4, d9.2.1 7 (by decide), c8.2.1 7 (by decide), g6 7 (by decide), h7, d6, c4,
      c8.1 14 (by decide), g4 14 (by decide), h14, c8.2.1 5 (by decide), g6 5 (by decide), h5]
    push_cast; ring
  -- 5. the columns
  obtain ⟨u5, hu5, f1, f2, f3, f4, f5⟩ :=
    ej_loop Q off q hE k L kk p₀ K1 P1 hK1 hP1 τ ξ v (‖v‖ ^ 2) rfl Hb vb Fb Cb Tb PNb Gb TGb Eb
      ⟨b1, b2, b3, b4, b5, b6⟩ hHv hvt hH0 s4 e1 e2
      (by rw [Q4 0 (by decide), h0]) (by rw [Q4 1 (by decide), h1]) (by rw [Q4 3 (by decide), h3])
      (by rw [Q4 14 (by decide), h14]) (by rw [Q4 15 (by decide), h15]) (by rw [Q4 24 (by decide), h24]) e5
      (by rw [Q4 36 (by decide), h36]) (by rw [Q4 37 (by decide), h37]) (by rw [Q4 39 (by decide), h39])
      (by rw [Q4 40 (by decide), h40]) (by rw [Q4 41 (by decide), h41]) (by rw [Q4 42 (by decide), h42])
      (by rw [Q4 43 (by decide), h43]) (by rw [Q4 44 (by decide), h44]) (by rw [Q4 45 (by decide), h45])
      (by rw [Q4 46 (by decide), h46]) (by rw [Q4 48 (by decide), h48]) (by rw [Q4 51 (by decide), h51])
      (by rw [e6.2.1 6 (by decide), d9.2.1 6 (by decide), c8.2.1 6 (by decide), g6 6 (by decide), h6])
      (by rw [e6.2.1 7 (by decide), d9.2.1 7 (by decide), c8.2.1 7 (by decide), g6 7 (by decide), h7]) r18
      (fun r j => by
        have : (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) < ((2 ^ k * 2 ^ k : ℕ) : ℤ) := by
          exact_mod_cast idx_ltE r.isLt j.isLt
        rw [M4 _ (nP _ (by omega))]; exact hcol r j)
      (fun c => by
        have : ((c : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast c.isLt
        rw [M4 _ (nP _ (by omega))]; exact hv c)
      (fun i hi => by
        have : (i : ℤ) < K1 := by exact_mod_cast hi
        rw [M4 _ (nP _ (by omega))]; exact hF i hi)
      (by
        intro ℓ r
        have a1 : (0 : ℤ) ≤ ((ℓ : ℕ) : ℤ) * 2 ^ k + ((r : ℕ) : ℤ) := by positivity
        have a2 : (0 : ℤ) < 2 ^ k := by positivity
        rw [M4 _ (nP _ (by omega))]; exact hS ℓ r)
      (fun i hi => by
        rw [e6.2.2.1 _ (fun h => h), d4 i hi, c5, g6 6 (by decide), h6, zero_sub])
  set s5 := run Q s4 detTape u5 with hs5
  -- 6. the next entry
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, _⟩ := evn Q off q hE s5 f1 f2
  refine ⟨3 + u2 + u3 + u4 + u5 + 2, by unfold VB; omega, ?_⟩
  have e : run Q s detTape (3 + u2 + u3 + u4 + u5 + 2) = run Q s5 detTape 2 := by
    rw [run_add, run_add, run_add, run_add, run_add, ← hs1, ← hs2, ← hs3, ← hs4, ← hs5]
  rw [e]
  refine ⟨k1, k2, by rw [k8, f3, e3, d3, c3, g9]; ring, ?_, ?_, ?_⟩
  · rw [k3, f5.1 51 (by decide), Q4 51 (by decide), h51, f5.1 3 (by decide), Q4 3 (by decide), h3]
  · rw [k5, f4, e6.2.1 13 (by decide), d9.2.1 13 (by decide), c8.2.1 13 (by decide), g6 13 (by decide)]
  · have m1 : Fr Wp Wr Wm s s1 :=
      ⟨fun y hy => g4 y (fun e => hy (by simp [Wp, e])), fun y hy => g6 y (fun e => hy (by simp [Wr, e])),
        fun z _ => by rw [g7], g8⟩
    have m2 := fr_mono c8 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide) (fun _ h => h.elim)
    have m3 := fr_mono d9 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide)
      (fun z hz => ⟨by omega, by omega⟩)
    have m4 := fr_mono e6 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide) (fun _ h => h.elim)
    have m5 := fr_mono f5 (Wp' := Wp) (Wr' := Wr) (Wm' := Wm) (by decide) (by decide)
      (fun z hz => by rcases hz with ⟨h, h'⟩ | ⟨h, h'⟩ <;> exact ⟨by omega, by omega⟩)
    have m6 : Fr Wp Wr Wm s5 (run Q s5 detTape 2) :=
      ⟨fun y hy => k4 y (fun e => hy (by simp [Wp, e])), fun y _ => by rw [k5], fun z _ => by rw [k6], k7⟩
    exact fr_trans (fr_trans (fr_trans (fr_trans (fr_trans m1 m2) m3) m4) m5) m6

end DetANN.Supplement.Thm32

-- ===== T32_EvalF =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP Finset

lemma BL_le {d K1 P1 M : ℕ} (hd : d ≤ M) (hK : K1 ≤ M) (hP : P1 ≤ M) (hM : 4 ≤ M) :
    BL d K1 P1 ≤ 36 * M ^ 3 := by
  calc BL d K1 P1 ≤ BL M M M := by unfold BL; gcongr
    _ ≤ 36 * M ^ 3 := by
      unfold BL
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
      ring_nf
      nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

lemma cube_facts {M : ℕ} (hM : 4 ≤ M) : 64 ≤ M ^ 3 ∧ M ≤ M ^ 3 :=
  ⟨by calc (64 : ℕ) = 4 ^ 3 := by norm_num
        _ ≤ M ^ 3 := Nat.pow_le_pow_left hM 3, Nat.le_self_pow (by norm_num) M⟩

lemma BJ_le {d L K1 P1 M : ℕ} (hd : d ≤ M) (hK : K1 ≤ M) (hP : P1 ≤ M) (hM : 4 ≤ M) :
    BJ d L K1 P1 ≤ 37 * (L + 1) * M ^ 3 := by
  have h1 := BL_le hd hK hP hM
  obtain ⟨h2, h3⟩ := cube_facts hM
  have h4 : L * BL d K1 P1 ≤ 36 * (L * M ^ 3) := by
    calc L * BL d K1 P1 ≤ L * (36 * M ^ 3) := Nat.mul_le_mul_left L h1
      _ = 36 * (L * M ^ 3) := by ring
  rw [show 37 * (L + 1) * M ^ 3 = 37 * (L * M ^ 3) + 37 * M ^ 3 by ring]
  unfold BJ
  generalize L * BL d K1 P1 = A at *
  generalize L * M ^ 3 = B at *
  generalize M ^ 3 = C at *
  omega

lemma VB_le {d L K1 P1 P2 M : ℕ} (hd : d ≤ M) (hK : K1 ≤ M) (hP : P1 ≤ M) (hP2 : P2 ≤ M) (hM : 4 ≤ M) :
    VB d L K1 P1 P2 ≤ 37 * ((d + 1) * (L + 1) * M ^ 3) := by
  have hBJ := BJ_le (L := L) hd hK hP hM
  obtain ⟨h2, h3⟩ := cube_facts hM
  have h5 : d * BJ d L K1 P1 ≤ 37 * (d * L * M ^ 3) + 37 * (d * M ^ 3) := by
    calc d * BJ d L K1 P1 ≤ d * (37 * (L + 1) * M ^ 3) := Nat.mul_le_mul_left d hBJ
      _ = 37 * (d * L * M ^ 3) + 37 * (d * M ^ 3) := by ring
  rw [show 37 * ((d + 1) * (L + 1) * M ^ 3) =
    37 * (d * L * M ^ 3) + 37 * (d * M ^ 3) + 37 * (L * M ^ 3) + 37 * M ^ 3 by ring]
  unfold VB
  generalize d * BJ d L K1 P1 = A at *
  generalize d * L * M ^ 3 = B at *
  generalize d * M ^ 3 = B2 at *
  generalize L * M ^ 3 = B3 at *
  generalize M ^ 3 = C at *
  omega

lemma total_le (N d L p₀ : ℕ) (hd : 1 ≤ d) :
    2 + N * VB d L (4 * p₀ + 1) (2 * p₀ + 1) (2 * p₀) + 1 + 2 ≤ evalB N d L p₀ := by
  have hM : 4 ≤ d + 4 * p₀ + 3 := by omega
  have hV := VB_le (L := L) (by omega : d ≤ d + 4 * p₀ + 3) (by omega : 4 * p₀ + 1 ≤ d + 4 * p₀ + 3)
    (by omega : 2 * p₀ + 1 ≤ d + 4 * p₀ + 3) (by omega : 2 * p₀ ≤ d + 4 * p₀ + 3) hM
  obtain ⟨h2, _⟩ := cube_facts hM
  have hX : 64 ≤ (d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3 := by
    calc 64 ≤ (d + 4 * p₀ + 3) ^ 3 := h2
      _ ≤ (d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3 :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have h7 : N * VB d L (4 * p₀ + 1) (2 * p₀ + 1) (2 * p₀) ≤
      37 * (N * ((d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3)) := by
    calc _ ≤ N * (37 * ((d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3)) := Nat.mul_le_mul_left N hV
      _ = _ := by ring
  rw [show evalB N d L p₀ = 100 * (N * ((d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3)) +
    100 * ((d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3) by unfold evalB; ring]
  generalize N * VB d L (4 * p₀ + 1) (2 * p₀ + 1) (2 * p₀) = A at *
  generalize N * ((d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3) = B at *
  generalize (d + 1) * (L + 1) * (d + 4 * p₀ + 3) ^ 3 = C at *
  omega

lemma take_sum_succ {α : Type*} (f : α → ℝ) (l : List α) (t : ℕ) (ht : t < l.length) :
    ((l.take (t + 1)).map f).sum = ((l.take t).map f).sum + f l[t] := by
  rw [List.take_succ, List.map_append, List.sum_append, List.getElem?_eq_getElem ht]; simp

theorem eval_spec_pf :
    ∀ (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (k L p₀ kk : ℕ) (hL : 1 ≤ L)
    (hkk : kk < L * 2 ^ k) (τ : ℝ) (hτ : 0 < τ) (l : List (EuclideanSpace ℝ (Fin (2 ^ k))))
    (hl : l.Nodup) (hl0 : ∀ v ∈ l, v ≠ 0) (ξ : Fin L → Fin (2 ^ k) → Bool) (Hb Db t0 ret : ℤ)
    (hHD : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ Db) (hDt : Db + ((l.length * 2 ^ k : ℕ) : ℤ) ≤ t0)
    (hH0 : 0 ≤ Hb) (hret : ret = 0 ∨ ret = 1) (s : State)
    (hpc : s.core.pc = off + 206) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h3 : s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ))
    (h14 : s.core.ptrs 14 = L) (h15 : s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1)
    (h24 : s.core.ptrs 24 = Hb) (h26 : s.core.ptrs 26 = Db)
    (h27 : s.core.ptrs 27 = Db + ((l.length * 2 ^ k : ℕ) : ℤ))
    (h36 : s.core.ptrs 36 = 2 * (p₀ : ℤ)) (h37 : s.core.ptrs 37 = 2 * (p₀ : ℤ) + 1)
    (h39 : s.core.ptrs 39 = 4 * (p₀ : ℤ) + 1) (h40 : s.core.ptrs 40 = t0)
    (h41 : s.core.ptrs 41 = t0 + (4 * (p₀ : ℤ) + 1))
    (h42 : s.core.ptrs 42 = t0 + 2 * (4 * (p₀ : ℤ) + 1))
    (h43 : s.core.ptrs 43 = t0 + 3 * (4 * (p₀ : ℤ) + 1))
    (h44 : s.core.ptrs 44 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + (2 * (p₀ : ℤ) + 1))
    (h45 : s.core.ptrs 45 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 2 * (2 * (p₀ : ℤ) + 1))
    (h46 : s.core.ptrs 46 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 3 * (2 * (p₀ : ℤ) + 1))
    (h48 : s.core.ptrs 48 = kk) (h50 : s.core.ptrs 50 = ret)
    (h5 : s.core.regs 5 = τ) (h6 : s.core.regs 6 = 0) (h7 : s.core.regs 7 = 1)
    (hcol : ∀ r j : Fin (2 ^ k), s.core.mem (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r)
    (hT : TableAt s.core.mem Db l)
    (hF : ∀ i : ℕ, i < 4 * p₀ + 1 → s.core.mem (t0 + i) = (i.factorial : ℝ))
    (hS : SignsAt s.core.mem L k ξ),
    ∃ t, t ≤ evalB l.length (2 ^ k) L p₀ ∧
      (ret = 0 → (run Q s detTape t).core.pc = off + 194) ∧
      (ret = 1 → (run Q s detTape t).core.pc = off + 198) ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.regs 13 =
        lemma62Expr (sylvester k) L τ p₀ l.toFinset (prefixMask L (2 ^ k) (kk + 1)) ξ ∧
      (∀ y, y ≠ 5 → y ≠ 10 → y ≠ 11 → y ≠ 12 → y ≠ 16 → y ≠ 17 → y ≠ 18 → y ≠ 19 → y ≠ 20 →
        y ≠ 31 → (y < 51 ∨ 58 < y) → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → (y < 13 ∨ 24 < y) → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      (∀ z, (z < t0 + (4 * (p₀ : ℤ) + 1) ∨
          t0 + 3 * (4 * (p₀ : ℤ) + 1) + 4 * (2 * (p₀ : ℤ) + 1) ≤ z) →
        (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by
  intro Q off q hE k L p₀ kk hL hkk τ hτ l hl hl0 ξ Hb Db t0 ret hHD hDt hH0 hret s hpc hh h0 h1 h3 h14 h15 h24 h26 h27 h36 h37 h39 h40 h41 h42 h43 h44 h45 h46 h48 h50 h5 h6 h7 hcol hT hF hS
  -- the layout
  set Cb : ℤ := t0 + (4 * (p₀ : ℤ) + 1) with hCb
  set Tb : ℤ := t0 + 2 * (4 * (p₀ : ℤ) + 1) with hTb
  set PNb : ℤ := t0 + 3 * (4 * (p₀ : ℤ) + 1) with hPNb
  set Gb : ℤ := t0 + 3 * (4 * (p₀ : ℤ) + 1) + (2 * (p₀ : ℤ) + 1) with hGb
  set TGb : ℤ := t0 + 3 * (4 * (p₀ : ℤ) + 1) + 2 * (2 * (p₀ : ℤ) + 1) with hTGb
  set Eb : ℤ := t0 + 3 * (4 * (p₀ : ℤ) + 1) + 3 * (2 * (p₀ : ℤ) + 1) with hEb
  have hb : Cb = t0 + ((4 * p₀ + 1 : ℕ) : ℤ) ∧ Tb = Cb + ((4 * p₀ + 1 : ℕ) : ℤ) ∧
      PNb = Tb + ((4 * p₀ + 1 : ℕ) : ℤ) ∧ Gb = PNb + ((2 * p₀ + 1 : ℕ) : ℤ) ∧
      TGb = Gb + ((2 * p₀ + 1 : ℕ) : ℤ) ∧ Eb = TGb + ((2 * p₀ + 1 : ℕ) : ℤ) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring
  have hd0 : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  have hdd : (0 : ℤ) ≤ (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) := by positivity
  have hDb : Hb + (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) ≤ Db := hHD
  have hND : Db + ((l.length * (2 ^ k) : ℕ) : ℤ) ≤ t0 := hDt
  let Wp : Finset ℕ := {5, 10, 11, 12, 16, 17, 18, 19, 20, 31, 51, 52, 53, 54, 55, 56, 57, 58}
  let Wr : Finset ℕ := {0, 1, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}
  let Wm : ℤ → Prop := fun z => Cb ≤ z ∧ z < Eb + ((2 * p₀ + 1 : ℕ) : ℤ)
  let f : EuclideanSpace ℝ (Fin (2 ^ k)) → ℝ := fun v =>
    ∑ j : Fin (2 ^ k), termVJ (sylvester k) τ p₀ (prefixMask L (2 ^ k) (kk + 1)) ξ v j
  have hnW : ∀ z, z < Cb → ¬ Wm z := fun z hz h => by omega
  have hCpos : (0 : ℤ) ≤ t0 := by
    have : (0 : ℤ) ≤ ((l.length * (2 ^ k) : ℕ) : ℤ) := by positivity
    omega
  -- the invariant
  let Inv : ℕ → State → Prop := fun t s' => s'.core.ptrs 51 = Db + ((t * (2 ^ k) : ℕ) : ℤ) ∧
    s'.core.regs 13 = ((l.take t).map f).sum ∧ Fr Wp Wr Wm s s'
  have hst : ∀ t s', t < l.length → Inv t s' → s'.core.pc = off + 208 → s'.halted = false →
      ∃ u, u ≤ VB (2 ^ k) L (4 * p₀ + 1) (2 * p₀ + 1) (2 * p₀) ∧ (run Q s' detTape u).core.pc = off + 208 ∧
        (run Q s' detTape u).halted = false ∧
        (run Q s' detTape u).work = s'.work + u ∧ Inv (t + 1) (run Q s' detTape u) := by
    intro t s' ht ⟨i1, i2, i3⟩ hpc' hh'
    have P : ∀ y, y ∉ Wp → s'.core.ptrs y = s.core.ptrs y := i3.1
    have R : ∀ y, y ∉ Wr → s'.core.regs y = s.core.regs y := i3.2.1
    have M : ∀ z, ¬ Wm z → s'.core.mem z = s.core.mem z := i3.2.2.1
    have hcast : ((t * (2 ^ k) : ℕ) : ℤ) + ((2 ^ k : ℕ) : ℤ) ≤ ((l.length * (2 ^ k) : ℕ) : ℤ) := by
      have := Nat.mul_le_mul_right (2 ^ k) (show t + 1 ≤ l.length by omega)
      rw [Nat.add_mul, one_mul] at this
      exact_mod_cast this
    have htd : (0 : ℤ) ≤ ((t * (2 ^ k) : ℕ) : ℤ) := by positivity
    obtain ⟨u, hu, a1, a2, a3, a4, a5, a6⟩ :=
      ev_body Q off q hE k L kk p₀ (4 * p₀ + 1) (2 * p₀ + 1) rfl rfl τ ξ l[t] Hb (Db + ((t * (2 ^ k) : ℕ) : ℤ))
        (Db + ((l.length * (2 ^ k) : ℕ) : ℤ)) t0 Cb Tb PNb Gb TGb Eb hb (by omega) (by omega) hH0 (by omega)
        s' hpc' hh'
        (by rw [P 0 (by decide), h0]) (by rw [P 1 (by decide), h1]) (by rw [P 3 (by decide), h3])
        (by rw [P 14 (by decide), h14]) (by rw [P 15 (by decide), h15]) (by rw [P 24 (by decide), h24])
        (by rw [P 27 (by decide), h27])
        (by rw [P 36 (by decide), h36]; push_cast; ring) (by rw [P 37 (by decide), h37]; push_cast; ring)
        (by rw [P 39 (by decide), h39]; push_cast; ring) (by rw [P 40 (by decide), h40])
        (by rw [P 41 (by decide), h41]) (by rw [P 42 (by decide), h42]) (by rw [P 43 (by decide), h43])
        (by rw [P 44 (by decide), h44]) (by rw [P 45 (by decide), h45]) (by rw [P 46 (by decide), h46])
        (by rw [P 48 (by decide), h48]) i1
        (by rw [R 5 (by decide), h5]) (by rw [R 6 (by decide), h6]) (by rw [R 7 (by decide), h7])
        (fun r j => by
          have : (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ) < (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) := by
            exact_mod_cast idx_ltE r.isLt j.isLt
          rw [M _ (hnW _ (by omega))]; exact hcol r j)
        (fun c => by
          have hc : ((c : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast c.isLt
          rw [M _ (hnW _ (by omega))]
          rw [show Db + ((t * (2 ^ k) : ℕ) : ℤ) + ((c : ℕ) : ℤ) = Db + ((t * 2 ^ k + c : ℕ) : ℤ) by push_cast; ring]
          exact hT t l[t] (List.getElem?_eq_getElem ht) c)
        (fun i hi => by
          have : (i : ℤ) < ((4 * p₀ + 1 : ℕ) : ℤ) := by exact_mod_cast hi
          rw [M _ (hnW _ (by push_cast at this ⊢; omega))]; exact hF i hi)
        (by
          intro ℓ r
          have b1 : (0 : ℤ) ≤ ((ℓ : ℕ) : ℤ) * 2 ^ k + ((r : ℕ) : ℤ) := by positivity
          have b2 : (0 : ℤ) < 2 ^ k := by positivity
          rw [M _ (hnW _ (by omega))]; exact hS ℓ r)
    refine ⟨u, hu, a1, a2, a3, by rw [a4]; push_cast; ring, by rw [a5, i2, take_sum_succ f l t ht], ?_⟩
    exact fr_trans i3 (fr_mono a6 (le_refl _) (le_refl _) (fun z hz => ⟨hz.1, by push_cast; omega⟩))
  -- start
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ := ev_init Q off q hE s hpc hh
  set s1 := run Q s detTape 2 with hs1
  have I0 : Inv 0 s1 := ⟨by rw [g3, h26]; simp, by rw [g5]; simp,
    ⟨fun y hy => g4 y (fun e => hy (by simp [Wp, e])), fun y hy => g6 y (fun e => hy (by simp [Wr, e])),
      fun z _ => by rw [g7], g8⟩⟩
  obtain ⟨u, hu, a1, a2, a3, c1, c2, c3⟩ :=
    loop_inv (Q := Q) Inv l.length (VB (2 ^ k) L (4 * p₀ + 1) (2 * p₀ + 1) (2 * p₀)) hst l.length 0 s1 (by omega) I0 g1 g2
  set s2 := run Q s1 detTape u with hs2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, _⟩ :=
    ev_exit Q off q hE s2 a1 a2 (by rw [c1, c3.1 27 (by decide), h27])
  set s3 := run Q s2 detTape 1 with hs3
  have hval : s3.core.regs 13 =
      lemma62Expr (sylvester k) L τ p₀ l.toFinset (prefixMask L (2 ^ k) (kk + 1)) ξ := by
    rw [e4, c2, List.take_length, lemma62_eq _ _ _ _ _ hl]
  have hd1 : 1 ≤ (2 ^ k) := Nat.one_le_two_pow
  have hT : 2 + u + 1 + 2 ≤ evalB l.length (2 ^ k) L p₀ := by
    have := total_le l.length (2 ^ k) L p₀ hd1
    have : u ≤ l.length * VB (2 ^ k) L (4 * p₀ + 1) (2 * p₀ + 1) (2 * p₀) := hu
    omega
  -- the frame, read off
  have FR : ∀ s4 : State, s4.core.ptrs = s3.core.ptrs → s4.core.regs = s3.core.regs →
      s4.core.mem = s3.core.mem → s4.integerMemory = s3.integerMemory →
      (∀ y, y ≠ 5 → y ≠ 10 → y ≠ 11 → y ≠ 12 → y ≠ 16 → y ≠ 17 → y ≠ 18 → y ≠ 19 → y ≠ 20 →
        y ≠ 31 → (y < 51 ∨ 58 < y) → s4.core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → (y < 13 ∨ 24 < y) → s4.core.regs y = s.core.regs y) ∧
      (∀ z, (z < t0 + (4 * (p₀ : ℤ) + 1) ∨
          t0 + 3 * (4 * (p₀ : ℤ) + 1) + 4 * (2 * (p₀ : ℤ) + 1) ≤ z) → s4.core.mem z = s.core.mem z) ∧
      s4.integerMemory = s.integerMemory := by
    intro s4 q1 q2 q3 q4
    refine ⟨fun y y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 => ?_, fun y y1 y2 y3 => ?_, fun z hz => ?_, ?_⟩
    · rw [q1, e3, c3.1 y (by simp only [Wp, Finset.mem_insert, Finset.mem_singleton]; omega)]
    · rw [q2, e4, c3.2.1 y (by simp only [Wr, Finset.mem_insert, Finset.mem_singleton]; omega)]
    · rw [q3, e5, c3.2.2.1 z (by rintro ⟨h, h'⟩; push_cast at h'; omega)]
    · rw [q4, e6, c3.2.2.2]
  rcases hret with rfl | rfl
  · obtain ⟨k1, k2, k3, k4, k5, k6, k7, _⟩ :=
      eret0 Q off q hE s3 e1 e2 (by rw [e3, c3.1 50 (by decide), c3.1 0 (by decide), h50, h0])
    refine ⟨2 + u + 1 + 1, by omega, ?_⟩
    rw [run_add, run_add, run_add, ← hs1, ← hs2, ← hs3]
    obtain ⟨F1, F2, F3, F4⟩ := FR _ k3 k4 k5 k6
    exact ⟨fun _ => k1, fun h => absurd h (by norm_num), k2, by rw [k4, hval], F1, F2, F3, F4,
      by rw [k7, e7, a3, g9]; ring⟩
  · obtain ⟨k1, k2, k3, k4, k5, k6, k7, _⟩ :=
      eret1 Q off q hE s3 e1 e2 (by rw [e3, c3.1 50 (by decide), c3.1 0 (by decide), h50, h0]; norm_num)
    refine ⟨2 + u + 1 + 2, by omega, ?_⟩
    rw [run_add, run_add, run_add, ← hs1, ← hs2, ← hs3]
    obtain ⟨F1, F2, F3, F4⟩ := FR _ k3 k4 k5 k6
    exact ⟨fun h => absurd h (by norm_num), fun _ => k1, k2, by rw [k4, hval], F1, F2, F3, F4,
      by rw [k7, e7, a3, g9]; ring⟩

end DetANN.Supplement.Thm32

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

theorem _root_.solution :
    ∀ (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (k L p₀ kk : ℕ) (hL : 1 ≤ L)
    (hkk : kk < L * 2 ^ k) (τ : ℝ) (hτ : 0 < τ) (l : List (EuclideanSpace ℝ (Fin (2 ^ k))))
    (hl : l.Nodup) (hl0 : ∀ v ∈ l, v ≠ 0) (ξ : Fin L → Fin (2 ^ k) → Bool) (Hb Db t0 ret : ℤ)
    (hHD : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ Db) (hDt : Db + ((l.length * 2 ^ k : ℕ) : ℤ) ≤ t0)
    (hH0 : 0 ≤ Hb) (hret : ret = 0 ∨ ret = 1) (s : State)
    (hpc : s.core.pc = off + 206) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h3 : s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ))
    (h14 : s.core.ptrs 14 = L) (h15 : s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1)
    (h24 : s.core.ptrs 24 = Hb) (h26 : s.core.ptrs 26 = Db)
    (h27 : s.core.ptrs 27 = Db + ((l.length * 2 ^ k : ℕ) : ℤ))
    (h36 : s.core.ptrs 36 = 2 * (p₀ : ℤ)) (h37 : s.core.ptrs 37 = 2 * (p₀ : ℤ) + 1)
    (h39 : s.core.ptrs 39 = 4 * (p₀ : ℤ) + 1) (h40 : s.core.ptrs 40 = t0)
    (h41 : s.core.ptrs 41 = t0 + (4 * (p₀ : ℤ) + 1))
    (h42 : s.core.ptrs 42 = t0 + 2 * (4 * (p₀ : ℤ) + 1))
    (h43 : s.core.ptrs 43 = t0 + 3 * (4 * (p₀ : ℤ) + 1))
    (h44 : s.core.ptrs 44 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + (2 * (p₀ : ℤ) + 1))
    (h45 : s.core.ptrs 45 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 2 * (2 * (p₀ : ℤ) + 1))
    (h46 : s.core.ptrs 46 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 3 * (2 * (p₀ : ℤ) + 1))
    (h48 : s.core.ptrs 48 = kk) (h50 : s.core.ptrs 50 = ret)
    (h5 : s.core.regs 5 = τ) (h6 : s.core.regs 6 = 0) (h7 : s.core.regs 7 = 1)
    (hcol : ∀ r j : Fin (2 ^ k), s.core.mem (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r)
    (hT : TableAt s.core.mem Db l)
    (hF : ∀ i : ℕ, i < 4 * p₀ + 1 → s.core.mem (t0 + i) = (i.factorial : ℝ))
    (hS : SignsAt s.core.mem L k ξ),
    ∃ t, t ≤ evalB l.length (2 ^ k) L p₀ ∧
      (ret = 0 → (run Q s detTape t).core.pc = off + 194) ∧
      (ret = 1 → (run Q s detTape t).core.pc = off + 198) ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.regs 13 =
        lemma62Expr (sylvester k) L τ p₀ l.toFinset (prefixMask L (2 ^ k) (kk + 1)) ξ ∧
      (∀ y, y ≠ 5 → y ≠ 10 → y ≠ 11 → y ≠ 12 → y ≠ 16 → y ≠ 17 → y ≠ 18 → y ≠ 19 → y ≠ 20 →
        y ≠ 31 → (y < 51 ∨ 58 < y) → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → (y < 13 ∨ 24 < y) → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      (∀ z, (z < t0 + (4 * (p₀ : ℤ) + 1) ∨
          t0 + 3 * (4 * (p₀ : ℤ) + 1) + 4 * (2 * (p₀ : ℤ) + 1) ≤ z) →
        (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t :=
  DetANN.Supplement.Thm32.eval_spec_pf

end DetANN.Supplement.Thm32

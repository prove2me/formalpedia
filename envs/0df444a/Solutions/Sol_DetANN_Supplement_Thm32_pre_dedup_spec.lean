-- Prove2me | solution 1 for DetANN.Supplement.Thm32.pre_dedup_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-21T03:40:50.045648+00:00
-- url     : https://prove2.me/submissions/ee479024-21fb-4be2-b6c3-fc5ff918da68

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

lemma emb_preB {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB0 q off ++ preB1 q off ++ preB2 q off ++ preB3 q off ++ preB4 q off ++ preB5 q off ++ preB6 q off) (off + 64) := by
  have h := embeds_app_right hE
  simpa only [List.length_append, len_preA, len_fw, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_preB0 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB0 q off) (off + 64) := by
  have h := embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (emb_preB hE))))))
  simpa only [Nat.add_zero] using h

end DetANN.Supplement.Thm32

-- ===== T32_PreSegA =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- Empty table at `top`. -/
lemma dd_init (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 67) (hh : s.halted = false) :
    (run Q s detTape 5).core.pc = off + 72 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 10 = 0 ∧
      (run Q s detTape 5).core.ptrs 26 = s.core.ptrs 23 ∧
      (run Q s detTape 5).core.ptrs 27 = s.core.ptrs 23 ∧
      (run Q s detTape 5).core.ptrs 28 = 0 ∧
      (run Q s detTape 5).core.ptrs 29 = 1 ∧
      (∀ x, x ≠ 10 → x ≠ 26 → x ≠ 27 → x ≠ 28 → x ≠ 29 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- All pairs done; `top = Dend`. -/
lemma di_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 72) (hh : s.halted = false)
    (hb0 : s.core.ptrs 22 ≤ s.core.ptrs 10) :
    (run Q s detTape 2).core.pc = off + 115 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 23 = s.core.ptrs 27 ∧
      (∀ x, x ≠ 23 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma di_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 72) (hh : s.halted = false)
    (hb0 : s.core.ptrs 10 < s.core.ptrs 22) :
    (run Q s detTape 4).core.pc = off + 76 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 20 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 4).core.ptrs 30 = s.core.ptrs 29 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 20 → x ≠ 30 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma dj_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 76) (hh : s.halted = false)
    (hb0 : s.core.ptrs 22 ≤ s.core.ptrs 20) :
    (run Q s detTape 4).core.pc = off + 72 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 10 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 4).core.ptrs 29 = s.core.ptrs 29 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 10 → x ≠ 29 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma dj_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 76) (hh : s.halted = false)
    (hb0 : s.core.ptrs 20 < s.core.ptrs 22) :
    (run Q s detTape 2).core.pc = off + 78 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 31 = 0 ∧
      (∀ x, x ≠ 31 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- One coordinate of `P_i - P_j` at `Dend`. -/
lemma w_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (x y : ℝ) (s : State)
    (hpc : s.core.pc = off + 78) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 29 + s.core.ptrs 31) = x)
    (fr1 : s.core.mem (s.core.ptrs 30 + s.core.ptrs 31) = y)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3) :
    (run Q s detTape 10).core.pc = off + 78 ∧
      (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 11 = s.core.ptrs 27 + s.core.ptrs 31 ∧
      (run Q s detTape 10).core.ptrs 31 = s.core.ptrs 31 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 31 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs 0 = (x - y) ∧
      (run Q s detTape 10).core.regs 1 = y ∧
      (∀ x, x ≠ 0 → x ≠ 1 → (run Q s detTape 10).core.regs x = s.core.regs x) ∧
      (run Q s detTape 10).core.mem (s.core.ptrs 27 + s.core.ptrs 31) = (x - y) ∧
      (∀ z, z ≠ s.core.ptrs 27 + s.core.ptrs 31 → (run Q s detTape 10).core.mem z = s.core.mem z) ∧
      (run Q s detTape 10).integerMemory = s.integerMemory ∧
      (run Q s detTape 10).work = s.work + 10 ∧
      ∀ c ∈ cellsWritten Q s 10, c = (true, s.core.ptrs 27 + s.core.ptrs 31) := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 29 + ptrs 31 → mem z = x := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 30 + ptrs 31 → mem z = y := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma w_exit (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 78) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 31) :
    (run Q s detTape 2).core.pc = off + 89 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 32 = s.core.ptrs 26 ∧
      (∀ x, x ≠ 32 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Not found: append. -/
lemma e_new (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 89) (hh : s.halted = false)
    (hb0 : s.core.ptrs 27 ≤ s.core.ptrs 32) :
    (run Q s detTape 6).core.pc = off + 76 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
      (run Q s detTape 6).core.ptrs 27 = s.core.ptrs 27 + s.core.ptrs 3 ∧
      (run Q s detTape 6).core.ptrs 28 = s.core.ptrs 28 + 1 ∧
      (run Q s detTape 6).core.ptrs 30 = s.core.ptrs 30 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 20 → x ≠ 27 → x ≠ 28 → x ≠ 30 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma e_head (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 89) (hh : s.halted = false)
    (hb0 : s.core.ptrs 32 < s.core.ptrs 27) :
    (run Q s detTape 2).core.pc = off + 91 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 31 = 0 ∧
      (∀ x, x ≠ 31 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Equal: a duplicate. -/
lemma c_dup (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 91) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 31) :
    (run Q s detTape 4).core.pc = off + 76 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
      (run Q s detTape 4).core.ptrs 30 = s.core.ptrs 30 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 20 → x ≠ 30 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma c_mis1 (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 91) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 32 + s.core.ptrs 31) = a)
    (fr1 : s.core.mem (s.core.ptrs 27 + s.core.ptrs 31) = b)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3)
    (hb1 : ¬ (a - b) ≤ 0) :
    (run Q s detTape 10).core.pc = off + 89 ∧
      (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 11 = s.core.ptrs 27 + s.core.ptrs 31 ∧
      (run Q s detTape 10).core.ptrs 32 = s.core.ptrs 32 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 11 → x ≠ 32 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs 0 = a ∧
      (run Q s detTape 10).core.regs 1 = b ∧
      (run Q s detTape 10).core.regs 2 = (a - b) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → (run Q s detTape 10).core.regs x = s.core.regs x) ∧
      (run Q s detTape 10).core.mem = s.core.mem ∧
      (run Q s detTape 10).integerMemory = s.integerMemory ∧
      (run Q s detTape 10).work = s.work + 10 ∧
      cellsWritten Q s 10 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 32 + ptrs 31 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 27 + ptrs 31 → mem z = b := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma c_mis2 (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 91) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 32 + s.core.ptrs 31) = a)
    (fr1 : s.core.mem (s.core.ptrs 27 + s.core.ptrs 31) = b)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3)
    (hb1 : (a - b) ≤ 0)
    (hb2 : ¬ (b - a) ≤ 0) :
    (run Q s detTape 12).core.pc = off + 89 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 11 = s.core.ptrs 27 + s.core.ptrs 31 ∧
      (run Q s detTape 12).core.ptrs 32 = s.core.ptrs 32 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 11 → x ≠ 32 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs 0 = a ∧
      (run Q s detTape 12).core.regs 1 = b ∧
      (run Q s detTape 12).core.regs 2 = (b - a) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → (run Q s detTape 12).core.regs x = s.core.regs x) ∧
      (run Q s detTape 12).core.mem = s.core.mem ∧
      (run Q s detTape 12).integerMemory = s.integerMemory ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      cellsWritten Q s 12 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 32 + ptrs 31 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 27 + ptrs 31 → mem z = b := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma c_eq (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 91) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 32 + s.core.ptrs 31) = a)
    (fr1 : s.core.mem (s.core.ptrs 27 + s.core.ptrs 31) = b)
    (hb0 : s.core.ptrs 31 < s.core.ptrs 3)
    (hb1 : (a - b) ≤ 0)
    (hb2 : (b - a) ≤ 0) :
    (run Q s detTape 11).core.pc = off + 91 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 11 = s.core.ptrs 27 + s.core.ptrs 31 ∧
      (run Q s detTape 11).core.ptrs 31 = s.core.ptrs 31 + 1 ∧
      (∀ x, x ≠ 11 → x ≠ 31 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs 0 = a ∧
      (run Q s detTape 11).core.regs 1 = b ∧
      (run Q s detTape 11).core.regs 2 = (b - a) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → (run Q s detTape 11).core.regs x = s.core.regs x) ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      cellsWritten Q s 11 = ∅ := by
  have hS := emb_preB0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 32 + ptrs 31 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 27 + ptrs 31 → mem z = b := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

end DetANN.Supplement.Thm32

-- ===== T32_DedupMath =====
namespace DetANN.Supplement.Thm32

variable {d : ℕ}

lemma ddStep_length_le (l : List (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d)) :
    l.length ≤ (ddStep l v).length ∧ (ddStep l v).length ≤ l.length + 1 := by
  unfold ddStep; split_ifs <;> simp

lemma ddJ_length (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))),
      l.length ≤ (ddJ x i j kk l).length ∧ (ddJ x i j kk l).length ≤ l.length + kk := by
  intro kk
  induction kk with
  | zero => intro j l; simp [ddJ]
  | succ kk ih =>
    intro j l
    have h1 := ddStep_length_le l (x i - x j)
    have h2 := ih (j + 1) (ddStep l (x i - x j))
    simp only [ddJ]; omega

lemma ddI_length (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))),
      l.length ≤ (ddI x n i kk l).length ∧ (ddI x n i kk l).length ≤ l.length + kk * n := by
  intro kk
  induction kk with
  | zero => intro i l; simp [ddI]
  | succ kk ih =>
    intro i l
    have h1 := ddJ_length x i (n - (i + 1)) (i + 1) l
    have h2 := ih (i + 1) (ddJ x i (i + 1) (n - (i + 1)) l)
    simp only [ddI]
    have : n - (i + 1) ≤ n := Nat.sub_le _ _
    constructor
    · omega
    · have e : (kk + 1) * n = kk * n + n := by ring
      omega

lemma ddList_length (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : (ddList x n).length ≤ n * n := by
  have := (ddI_length x n n 0 []).2; simpa [ddList] using this

end DetANN.Supplement.Thm32

-- ===== T32_PreDedup =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

variable {d : ℕ}

lemma w_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (i j : ℕ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (Dend : ℤ) (m0 : ℤ → ℝ)
    (hxi : ∀ c : Fin d, m0 ((1 + i * d + c : ℕ) : ℤ) = x i c)
    (hxj : ∀ c : Fin d, m0 ((1 + j * d + c : ℕ) : ℤ) = x j c)
    (hpi : ((1 + i * d + d : ℕ) : ℤ) ≤ Dend) (hpj : ((1 + j * d + d : ℕ) : ℤ) ≤ Dend) :
    ∀ (kk c : ℕ) (s : State), c + kk = d → s.core.pc = off + 78 → s.halted = false →
      s.core.ptrs 31 = c → s.core.ptrs 3 = d → s.core.ptrs 29 = ((1 + i * d : ℕ) : ℤ) →
      s.core.ptrs 30 = ((1 + j * d : ℕ) : ℤ) → s.core.ptrs 27 = Dend →
      (∀ c' : Fin d, (c' : ℕ) < c → s.core.mem (Dend + (c' : ℕ)) = (x i - x j) c') →
      (∀ z, (z < Dend ∨ Dend + c ≤ z) → s.core.mem z = m0 z) →
      ∃ t, t ≤ 10 * kk + 2 ∧ (run Q s detTape t).core.pc = off + 89 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 32 = s.core.ptrs 26 ∧
        (∀ y, y ≠ 11 → y ≠ 31 → y ≠ 32 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (∀ c' : Fin d, (run Q s detTape t).core.mem (Dend + (c' : ℕ)) = (x i - x j) c') ∧
        (∀ z, (z < Dend ∨ Dend + d ≤ z) → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro c s hck hpc hh h31 h3 h29 h30 h27 hw hout
    have hc : c = d := by omega
    subst hc
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ := w_exit Q off q hE s hpc hh (by rw [h3, h31])
    exact ⟨2, by omega, g1, g2, g3, fun y _ _ y32 => g4 y y32, fun y _ _ => by rw [g5],
      fun c' => by rw [g6]; exact hw c' c'.isLt, fun z hz => by rw [g6]; exact hout z hz, g7, g8⟩
  | succ kk ih =>
    intro c s hck hpc hh h31 h3 h29 h30 h27 hw hout
    have hc : c < d := by omega
    have a0 : s.core.ptrs 29 + s.core.ptrs 31 = ((1 + i * d + c : ℕ) : ℤ) := by
      rw [h29, h31]; push_cast; ring
    have a1 : s.core.ptrs 30 + s.core.ptrs 31 = ((1 + j * d + c : ℕ) : ℤ) := by
      rw [h30, h31]; push_cast; ring
    have b0 : ((1 + i * d + c : ℕ) : ℤ) < Dend := by
      have : ((1 + i * d + c : ℕ) : ℤ) < ((1 + i * d + d : ℕ) : ℤ) := by exact_mod_cast (by omega)
      omega
    have b1 : ((1 + j * d + c : ℕ) : ℤ) < Dend := by
      have : ((1 + j * d + c : ℕ) : ℤ) < ((1 + j * d + d : ℕ) : ℤ) := by exact_mod_cast (by omega)
      omega
    have e0 : s.core.mem (s.core.ptrs 29 + s.core.ptrs 31) = x i ⟨c, hc⟩ := by
      rw [a0, hout _ (Or.inl b0)]; exact hxi ⟨c, hc⟩
    have e1 : s.core.mem (s.core.ptrs 30 + s.core.ptrs 31) = x j ⟨c, hc⟩ := by
      rw [a1, hout _ (Or.inl b1)]; exact hxj ⟨c, hc⟩
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
      w_step Q off q hE _ _ s hpc hh e0 e1 (by rw [h31, h3]; exact_mod_cast hc)
    set s1 := run Q s detTape 10 with hs1
    rw [h27, h31] at g9 g10
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (c + 1) s1 (by omega) g1 g2 (by rw [g4, h31]; push_cast; ring)
        (by rw [g5 3 (by decide) (by decide), h3]) (by rw [g5 29 (by decide) (by decide), h29])
        (by rw [g5 30 (by decide) (by decide), h30]) (by rw [g5 27 (by decide) (by decide), h27])
        (by
          intro c' hc'
          rcases Nat.lt_or_ge (c' : ℕ) c with h | h
          · rw [g10 _ (by intro e; have := add_left_cancel e; omega)]; exact hw c' h
          · have e : c' = ⟨c, hc⟩ := Fin.ext (show (c' : ℕ) = c by omega)
            subst e; rw [g9]; simp)
        (by
          intro z hz
          rw [g10 z (by intro e; subst e; rcases hz with hz | hz <;> push_cast at hz <;> omega)]
          exact hout z (by rcases hz with hz | hz
                           · left; exact hz
                           · right; push_cast at hz; omega))
    refine ⟨10 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, by rw [q3, g5 26 (by decide) (by decide)],
      fun y a b e => by rw [q4 y a b e, g5 y a b], fun y a b => by rw [q5 y a b, g8 y a b], q6, q7,
      by rw [q8, g11], by rw [q9, g12]; ring⟩

lemma c_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off)
    (e Dend : ℤ) (u w : EuclideanSpace ℝ (Fin d)) :
    ∀ (kk c : ℕ) (s : State), c + kk = d → s.core.pc = off + 91 → s.halted = false →
      s.core.ptrs 31 = c → s.core.ptrs 3 = d → s.core.ptrs 32 = e → s.core.ptrs 27 = Dend →
      (∀ c' : Fin d, s.core.mem (e + (c' : ℕ)) = u c') →
      (∀ c' : Fin d, s.core.mem (Dend + (c' : ℕ)) = w c') →
      (∀ c' : Fin d, (c' : ℕ) < c → u c' = w c') →
      ∃ t, t ≤ 12 * kk + 4 ∧ (run Q s detTape t).halted = false ∧
        ((u = w ∧ (run Q s detTape t).core.pc = off + 76 ∧
            (run Q s detTape t).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
            (run Q s detTape t).core.ptrs 30 = s.core.ptrs 30 + d ∧
            (run Q s detTape t).core.ptrs 32 = e) ∨
          (u ≠ w ∧ (run Q s detTape t).core.pc = off + 89 ∧
            (run Q s detTape t).core.ptrs 20 = s.core.ptrs 20 ∧
            (run Q s detTape t).core.ptrs 30 = s.core.ptrs 30 ∧
            (run Q s detTape t).core.ptrs 32 = e + d)) ∧
        (∀ y, y ≠ 11 → y ≠ 20 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
          (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro c s hck hpc hh h31 h3 h32 h27 hu hw heq
    have hc : c = d := by omega
    subst hc
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ := c_dup Q off q hE s hpc hh (by rw [h3, h31])
    have huw : u = w := by
      ext c'; exact heq c' c'.isLt
    exact ⟨4, by omega, g2, Or.inl ⟨huw, g1, g3, by rw [g4, h3], by rw [g5 32 (by decide) (by decide), h32]⟩,
      fun y _ a _ _ _ => g5 y a (by assumption), fun y _ _ _ => by rw [g6], g7, g8, g9⟩
  | succ kk ih =>
    intro c s hck hpc hh h31 h3 h32 h27 hu hw heq
    have hc : c < d := by omega
    have ea : s.core.mem (s.core.ptrs 32 + s.core.ptrs 31) = u ⟨c, hc⟩ := by
      rw [h32, h31]; exact hu ⟨c, hc⟩
    have eb : s.core.mem (s.core.ptrs 27 + s.core.ptrs 31) = w ⟨c, hc⟩ := by
      rw [h27, h31]; exact hw ⟨c, hc⟩
    have hcd : s.core.ptrs 31 < s.core.ptrs 3 := by rw [h31, h3]; exact_mod_cast hc
    by_cases d1 : u ⟨c, hc⟩ - w ⟨c, hc⟩ ≤ 0
    · by_cases d2 : w ⟨c, hc⟩ - u ⟨c, hc⟩ ≤ 0
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
          c_eq Q off q hE _ _ s hpc hh ea eb hcd d1 d2
        set s1 := run Q s detTape 11 with hs1
        obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7⟩ :=
          ih (c + 1) s1 (by omega) g1 g2 (by rw [g4, h31]; push_cast; ring)
            (by rw [g5 3 (by decide) (by decide), h3]) (by rw [g5 32 (by decide) (by decide), h32])
            (by rw [g5 27 (by decide) (by decide), h27]) (fun c' => by rw [g10]; exact hu c')
            (fun c' => by rw [g10]; exact hw c')
            (by
              intro c' hc'
              rcases Nat.lt_or_ge (c' : ℕ) c with h | h
              · exact heq c' h
              · have e : c' = ⟨c, hc⟩ := Fin.ext (show (c' : ℕ) = c by omega)
                subst e; linarith)
        refine ⟨11 + t2, by omega, ?_⟩
        rw [run_add, ← hs1]
        refine ⟨q1, ?_, fun y a b c' e f => by rw [q3 y a b c' e f, g5 y a e],
          fun y a b c' => by rw [q4 y a b c', g9 y a b c'], by rw [q5, g10], by rw [q6, g11],
          by rw [q7, g12]; ring⟩
        rcases q2 with ⟨r1, r2, r3, r4, r5⟩ | ⟨r1, r2, r3, r4, r5⟩
        · exact Or.inl ⟨r1, r2, by rw [r3, g5 20 (by decide) (by decide)],
            by rw [r4, g5 30 (by decide) (by decide)], r5⟩
        · exact Or.inr ⟨r1, r2, by rw [r3, g5 20 (by decide) (by decide)],
            by rw [r4, g5 30 (by decide) (by decide)], r5⟩
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
          c_mis2 Q off q hE _ _ s hpc hh ea eb hcd d1 d2
        have hne : u ≠ w := fun e => by rw [e] at d2; simp at d2
        exact ⟨12, by omega, g2, Or.inr ⟨hne, g1, by rw [g5 20 (by decide) (by decide)],
          by rw [g5 30 (by decide) (by decide)], by rw [g4, h32, h3]⟩,
          fun y a _ _ _ b => g5 y a b, fun y a b c' => g9 y a b c', g10, g11, g12⟩
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
        c_mis1 Q off q hE _ _ s hpc hh ea eb hcd d1
      have hne : u ≠ w := fun e => by rw [e] at d1; simp at d1
      exact ⟨10, by omega, g2, Or.inr ⟨hne, g1, by rw [g5 20 (by decide) (by decide)],
        by rw [g5 30 (by decide) (by decide)], by rw [g4, h32, h3]⟩,
        fun y a _ _ _ b => g5 y a b, fun y a b c' => g9 y a b c', g10, g11, g12⟩

lemma table_step {mem : ℤ → ℝ} {Db Dend : ℤ} {l : List (EuclideanSpace ℝ (Fin d))}
    {w : EuclideanSpace ℝ (Fin d)} (hT : TableAt mem Db l) (hD : Dend = Db + ((l.length * d : ℕ) : ℤ))
    (hw : ∀ c : Fin d, mem (Dend + (c : ℕ)) = w c) : TableAt mem Db (ddStep l w) := by
  unfold ddStep
  split_ifs with h
  · exact hT
  · intro m v hv c
    rcases Nat.lt_or_ge m l.length with hm | hm
    · rw [List.getElem?_append_left hm] at hv; exact hT m v hv c
    · rw [List.getElem?_append_right hm] at hv
      have e : m - l.length = 0 := by
        by_contra hne
        have : (m - l.length) ≥ 1 := Nat.one_le_iff_ne_zero.2 hne
        rw [List.getElem?_eq_none (by simp; omega)] at hv; exact absurd hv (by simp)
      rw [e] at hv
      simp at hv; subst hv
      have hm' : m = l.length := by omega
      rw [hm', ← hw c, hD]; push_cast; ring_nf

lemma e_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (Db : ℤ) (l : List (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)) :
    ∀ (kk m : ℕ) (s : State), m + kk = l.length → s.core.pc = off + 89 → s.halted = false →
      s.core.ptrs 32 = Db + ((m * d : ℕ) : ℤ) → s.core.ptrs 3 = d →
      s.core.ptrs 27 = Db + ((l.length * d : ℕ) : ℤ) → s.core.ptrs 28 = l.length →
      TableAt s.core.mem Db l →
      (∀ c : Fin d, s.core.mem (Db + ((l.length * d : ℕ) : ℤ) + (c : ℕ)) = w c) →
      (∀ m' : ℕ, m' < m → l[m']? ≠ some w) →
      ∃ t, t ≤ kk * (12 * d + 8) + 6 ∧ (run Q s detTape t).core.pc = off + 76 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
        (run Q s detTape t).core.ptrs 30 = s.core.ptrs 30 + d ∧
        (run Q s detTape t).core.ptrs 27 = Db + (((ddStep l w).length * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 28 = (ddStep l w).length ∧
        (∀ y, y ≠ 11 → y ≠ 20 → y ≠ 27 → y ≠ 28 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
          (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro m s hmk hpc hh h32 h3 h27 h28 hT hw hne
    have hm : m = l.length := by omega
    subst hm
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, _⟩ :=
      e_new Q off q hE s hpc hh (by rw [h27, h32])
    have hnot : w ∉ l := by
      intro hw'
      obtain ⟨m', hm', e⟩ := List.getElem_of_mem hw'
      exact hne m' hm' (by rw [List.getElem?_eq_getElem hm', e])
    have hstep : ddStep l w = l ++ [w] := by simp [ddStep, hnot]
    refine ⟨6, by omega, g1, g2, g3, by rw [g6, h3], ?_, ?_, fun y a b c e f _ _ => g7 y b c e f,
      fun y _ _ _ => by rw [g8], g9, g10, g11⟩
    · rw [g4, h27, h3, hstep]; push_cast; simp; ring
    · rw [g5, h28, hstep]; push_cast; simp
  | succ kk ih =>
    intro m s hmk hpc hh h32 h3 h27 h28 hT hw hne
    have hm : m < l.length := by omega
    have hlt : s.core.ptrs 32 < s.core.ptrs 27 := by
      rw [h32, h27]
      have : m * d < l.length * d := Nat.mul_lt_mul_of_pos_right hm (by omega)
      have h' : ((m * d : ℕ) : ℤ) < ((l.length * d : ℕ) : ℤ) := by exact_mod_cast this
      omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ := e_head Q off q hE s hpc hh hlt
    set s1 := run Q s detTape 2 with hs1
    set u := l[m]'hm with hu
    obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7⟩ :=
      c_loop Q off q hE (Db + ((m * d : ℕ) : ℤ)) (Db + ((l.length * d : ℕ) : ℤ)) u w d 0 s1 (by omega)
        g1 g2 g3 (by rw [g4 3 (by decide), h3]) (by rw [g4 32 (by decide), h32])
        (by rw [g4 27 (by decide), h27])
        (fun c' => by
          rw [g6, show Db + ((m * d : ℕ) : ℤ) + ((c' : ℕ) : ℤ) = Db + ((m * d + c' : ℕ) : ℤ) by
            push_cast; ring]
          exact hT m u (List.getElem?_eq_getElem hm) c')
        (fun c' => by rw [g6]; exact hw c') (fun c' h => absurd h (Nat.not_lt_zero _))
    set s2 := run Q s1 detTape t2 with hs2
    rcases p2 with ⟨r1, r2, r3, r4, r5⟩ | ⟨r1, r2, r3, r4, r5⟩
    · -- found
      have hin : w ∈ l := by rw [← r1]; exact List.getElem_mem hm
      have hstep : ddStep l w = l := by simp [ddStep, hin]
      refine ⟨2 + t2, by
          have : (kk + 1) * (12 * d + 8) = kk * (12 * d + 8) + 12 * d + 8 := by ring
          omega, ?_⟩
      rw [run_add, ← hs1]
      refine ⟨r2, p1, by rw [r3, g4 20 (by decide)], by rw [r4, g4 30 (by decide)], ?_, ?_,
        fun y a b c e f g' h => by rw [p3 y a b f g' h, g4 y g'], fun y a b c => by rw [p4 y a b c, g5],
        by rw [p5, g6], by rw [p6, g7], by rw [p7, g8]; ring⟩
      · rw [hstep, p3 27 (by decide) (by decide) (by decide) (by decide) (by decide), g4 27 (by decide), h27]
      · rw [hstep, p3 28 (by decide) (by decide) (by decide) (by decide) (by decide), g4 28 (by decide), h28]
    · -- not this one: next
      obtain ⟨T3, hT3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
        ih (m + 1) s2 (by omega) r2 p1 (by rw [r5]; push_cast; ring)
          (by rw [p3 3 (by decide) (by decide) (by decide) (by decide) (by decide), g4 3 (by decide), h3])
          (by rw [p3 27 (by decide) (by decide) (by decide) (by decide) (by decide), g4 27 (by decide), h27])
          (by rw [p3 28 (by decide) (by decide) (by decide) (by decide) (by decide), g4 28 (by decide), h28])
          (by rw [p5, g6]; exact hT) (fun c => by rw [p5, g6]; exact hw c)
          (by
            intro m' hm'
            rcases Nat.lt_or_ge m' m with h | h
            · exact hne m' h
            · have : m' = m := by omega
              subst this
              rw [List.getElem?_eq_getElem hm]
              intro e; exact r1 (Option.some_injective _ e))
      refine ⟨2 + t2 + T3, by
          have : (kk + 1) * (12 * d + 8) = kk * (12 * d + 8) + 12 * d + 8 := by ring
          omega, ?_⟩
      have e2 : run Q s detTape (2 + t2) = s2 := by rw [run_add, ← hs1]
      rw [run_add, e2]
      refine ⟨q1, q2, by rw [q3, r3, g4 20 (by decide)], by rw [q4, r4, g4 30 (by decide)], q5, q6,
        fun y a b c e f g' h => by rw [q7 y a b c e f g' h, p3 y a b f g' h, g4 y g'],
        fun y a b c => by rw [q8 y a b c, p4 y a b c, g5], by rw [q9, p5, g6], by rw [q10, p6, g7],
        by rw [q11, p7, g8]; ring⟩

lemma pair_step (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n i j Lm : ℕ) (hi : i < n) (hj : j < n) (x : ℕ → EuclideanSpace ℝ (Fin d)) (m0 : ℤ → ℝ)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, m0 ((1 + i' * d + c : ℕ) : ℤ) = x i' c)
    (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db) (l : List (EuclideanSpace ℝ (Fin d)))
    (hLm : l.length ≤ Lm) (s : State) (hpc : s.core.pc = off + 76) (hh : s.halted = false)
    (h20 : s.core.ptrs 20 = j) (h22 : s.core.ptrs 22 = n) (h3 : s.core.ptrs 3 = d)
    (h29 : s.core.ptrs 29 = ((1 + i * d : ℕ) : ℤ)) (h30 : s.core.ptrs 30 = ((1 + j * d : ℕ) : ℤ))
    (h26 : s.core.ptrs 26 = Db) (h27 : s.core.ptrs 27 = Db + ((l.length * d : ℕ) : ℤ))
    (h28 : s.core.ptrs 28 = l.length) (hT : TableAt s.core.mem Db l)
    (hm0 : ∀ z, z < Db → s.core.mem z = m0 z) :
    ∃ t, t ≤ pairB d Lm ∧ (run Q s detTape t).core.pc = off + 76 ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 20 = j + 1 ∧
      (run Q s detTape t).core.ptrs 30 = ((1 + (j + 1) * d : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 27 = Db + (((ddStep l (x i - x j)).length * d : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 28 = (ddStep l (x i - x j)).length ∧
      (∀ y, y ≠ 11 → y ≠ 20 → y ≠ 27 → y ≠ 28 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
        (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      TableAt (run Q s detTape t).core.mem Db (ddStep l (x i - x j)) ∧
      (∀ z, z < Db → (run Q s detTape t).core.mem z = m0 z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by
  set Dend : ℤ := Db + ((l.length * d : ℕ) : ℤ) with hDend
  have hDD : Db ≤ Dend := by
    have : (0 : ℤ) ≤ ((l.length * d : ℕ) : ℤ) := by positivity
    simp only [hDend]; omega
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
    dj_head Q off q hE s hpc hh (by rw [h20, h22]; exact_mod_cast hj)
  set s1 := run Q s detTape 2 with hs1
  have hleDb : ∀ i' : ℕ, i' < n → ((1 + i' * d + d : ℕ) : ℤ) ≤ Db := by
    intro i' hi'
    have : 1 + i' * d + d ≤ 1 + n * d := by
      have := Nat.mul_le_mul_right d (show i' + 1 ≤ n by omega); nlinarith
    have : ((1 + i' * d + d : ℕ) : ℤ) ≤ ((1 + n * d : ℕ) : ℤ) := by exact_mod_cast this
    omega
  have hle : ∀ i' : ℕ, i' < n → ((1 + i' * d + d : ℕ) : ℤ) ≤ Dend :=
    fun i' hi' => le_trans (hleDb i' hi') hDD
  have hpt : ∀ i' : ℕ, i' < n → ∀ c : Fin d, s1.core.mem ((1 + i' * d + c : ℕ) : ℤ) = x i' c := by
    intro i' hi' c
    rw [g6, hm0 _ (by
      have := hleDb i' hi'
      have : ((1 + i' * d + (c : ℕ) : ℕ) : ℤ) < ((1 + i' * d + d : ℕ) : ℤ) := by exact_mod_cast (by omega)
      omega)]
    exact hx i' hi' c
  obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ :=
    w_loop Q off q hE i j x Dend s1.core.mem (hpt i hi) (hpt j hj) (hle i hi) (hle j hj) d 0 s1
      (by omega) g1 g2 g3 (by rw [g4 3 (by decide), h3]) (by rw [g4 29 (by decide), h29])
      (by rw [g4 30 (by decide), h30]) (by rw [g4 27 (by decide), h27])
      (fun c' h => absurd h (Nat.not_lt_zero _)) (fun z _ => rfl)
  set s2 := run Q s1 detTape t2 with hs2
  have f2 : ∀ y, y ≠ 11 → y ≠ 31 → y ≠ 32 → s2.core.ptrs y = s.core.ptrs y :=
    fun y a b c => by rw [p4 y a b c, g4 y b]
  have hT2 : TableAt s2.core.mem Db l := by
    intro m v hv c
    have hm : m < l.length := by
      by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hv; exact absurd hv (by simp)
    have : m * d + (c : ℕ) < l.length * d := by
      have := c.isLt
      calc m * d + (c : ℕ) < m * d + d := by omega
        _ = (m + 1) * d := by ring
        _ ≤ l.length * d := Nat.mul_le_mul_right _ hm
    have h' : ((m * d + (c : ℕ) : ℕ) : ℤ) < ((l.length * d : ℕ) : ℤ) := by exact_mod_cast this
    rw [p7 _ (Or.inl (by simp only [hDend]; omega)), g6]
    exact hT m v hv c
  obtain ⟨T3, hT3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
    e_loop Q off q hE hd1 Db l (x i - x j) l.length 0 s2 (by omega) p1 p2
      (by rw [p3, g4 26 (by decide), h26]; simp)
      (by rw [f2 3 (by decide) (by decide) (by decide), h3])
      (by rw [f2 27 (by decide) (by decide) (by decide), h27])
      (by rw [f2 28 (by decide) (by decide) (by decide), h28]) hT2 (fun c => p6 c)
      (fun m' h => absurd h (Nat.not_lt_zero _))
  set s3 := run Q s2 detTape T3 with hs3
  refine ⟨2 + t2 + T3, ?_, ?_⟩
  · unfold pairB
    have : l.length * (12 * d + 8) ≤ Lm * (12 * d + 8) := Nat.mul_le_mul_right _ hLm
    omega
  have e3 : run Q s detTape (2 + t2 + T3) = s3 := by
    rw [run_add, run_add, ← hs1, ← hs2, ← hs3]
  rw [e3]
  refine ⟨q1, q2, by rw [q3, f2 20 (by decide) (by decide) (by decide), h20],
    by rw [q4, f2 30 (by decide) (by decide) (by decide), h30]; push_cast; ring, q5, q6,
    fun y a b c e f g' h => by rw [q7 y a b c e f g' h, f2 y a g' h],
    fun y a b c => by rw [q8 y a b c, p5 y a b, g5], ?_, ?_, by rw [q10, p8, g7],
    by rw [q11, p9, g8]; ring⟩
  · rw [q9]; exact table_step hT2 rfl (fun c => p6 c)
  · intro z hz
    rw [q9, p7 z (Or.inl (by omega)), g6]; exact hm0 z hz

lemma dj_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n i Lm : ℕ) (hi : i < n) (x : ℕ → EuclideanSpace ℝ (Fin d)) (m0 : ℤ → ℝ)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, m0 ((1 + i' * d + c : ℕ) : ℤ) = x i' c)
    (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (s : State), j + kk = n →
      (ddJ x i j kk l).length ≤ Lm → s.core.pc = off + 76 → s.halted = false →
      s.core.ptrs 20 = j → s.core.ptrs 22 = n → s.core.ptrs 3 = d → s.core.ptrs 10 = i →
      s.core.ptrs 29 = ((1 + i * d : ℕ) : ℤ) → s.core.ptrs 30 = ((1 + j * d : ℕ) : ℤ) →
      s.core.ptrs 26 = Db → s.core.ptrs 27 = Db + ((l.length * d : ℕ) : ℤ) →
      s.core.ptrs 28 = l.length → TableAt s.core.mem Db l → (∀ z, z < Db → s.core.mem z = m0 z) →
      ∃ t, t ≤ kk * pairB d Lm + 4 ∧ (run Q s detTape t).core.pc = off + 72 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 10 = i + 1 ∧
        (run Q s detTape t).core.ptrs 29 = ((1 + (i + 1) * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 27 = Db + (((ddJ x i j kk l).length * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 28 = (ddJ x i j kk l).length ∧
        (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
          (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        TableAt (run Q s detTape t).core.mem Db (ddJ x i j kk l) ∧
        (∀ z, z < Db → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro j l s hjk hL hpc hh h20 h22 h3 h10 h29 h30 h26 h27 h28 hT hm0
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      dj_exit Q off q hE s hpc hh (by rw [h22, h20]; exact_mod_cast (by omega : n ≤ j))
    refine ⟨4, by omega, g1, g2, by rw [g3, h10], by rw [g4, h29, h3]; push_cast; ring,
      by rw [g5 27 (by decide) (by decide), h27]; rfl, by rw [g5 28 (by decide) (by decide), h28]; rfl,
      fun y a _ _ _ _ b _ _ _ => g5 y a b, fun y _ _ _ => by rw [g6], by rw [g7]; exact hT,
      fun z hz => by rw [g7]; exact hm0 z hz, g8, g9⟩
  | succ kk ih =>
    intro j l s hjk hL hpc hh h20 h22 h3 h10 h29 h30 h26 h27 h28 hT hm0
    have hj : j < n := by omega
    have hl1 : l.length ≤ Lm := by
      have a := (ddJ_length x i kk (j + 1) (ddStep l (x i - x j))).1
      have b := (ddStep_length_le l (x i - x j)).1
      simp only [ddJ] at hL; omega
    obtain ⟨t1, ht1, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ :=
      pair_step Q off q hE hd1 n i j Lm hi hj x m0 hx Db hDb l hl1 s hpc hh h20 h22 h3 h29 h30 h26 h27
        h28 hT hm0
    set s1 := run Q s detTape t1 with hs1
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
      ih (j + 1) (ddStep l (x i - x j)) s1 (by omega) (by simp only [ddJ] at hL; exact hL) p1 p2 p3
        (by rw [p7 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h22])
        (by rw [p7 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h3])
        (by rw [p7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h10])
        (by rw [p7 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h29]) p4
        (by rw [p7 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h26]) p5 p6 p9 p10
    refine ⟨t1 + t2, by
        have : (kk + 1) * pairB d Lm = kk * pairB d Lm + pairB d Lm := by ring
        omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, q3, q4, q5, q6, fun y a b c e f g' h i' j' => by
        rw [q7 y a b c e f g' h i' j', p7 y b c e f h i' j'],
      fun y a b c => by rw [q8 y a b c, p8 y a b c], q9, q10, by rw [q11, p11],
      by rw [q12, p12]; ring⟩

lemma di_loop (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n Lm : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (m0 : ℤ → ℝ)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, m0 ((1 + i' * d + c : ℕ) : ℤ) = x i' c)
    (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (s : State), i + kk = n →
      (ddI x n i kk l).length ≤ Lm → s.core.pc = off + 72 → s.halted = false →
      s.core.ptrs 10 = i → s.core.ptrs 22 = n → s.core.ptrs 3 = d →
      s.core.ptrs 29 = ((1 + i * d : ℕ) : ℤ) →
      s.core.ptrs 26 = Db → s.core.ptrs 27 = Db + ((l.length * d : ℕ) : ℤ) →
      s.core.ptrs 28 = l.length → TableAt s.core.mem Db l → (∀ z, z < Db → s.core.mem z = m0 z) →
      ∃ t, t ≤ kk * (n * pairB d Lm + 8) + 2 ∧ (run Q s detTape t).core.pc = off + 115 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 23 = Db + (((ddI x n i kk l).length * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 28 = (ddI x n i kk l).length ∧
        (run Q s detTape t).core.ptrs 26 = Db ∧
        (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 23 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 → y ≠ 31 →
          y ≠ 32 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
        (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
        TableAt (run Q s detTape t).core.mem Db (ddI x n i kk l) ∧
        (∀ z, z < Db → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro i l s hik hL hpc hh h10 h22 h3 h29 h26 h27 h28 hT hm0
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
      di_exit Q off q hE s hpc hh (by rw [h22, h10]; exact_mod_cast (by omega : n ≤ i))
    refine ⟨2, by omega, g1, g2, by rw [g3, h27]; rfl, by rw [g4 28 (by decide), h28]; rfl,
      by rw [g4 26 (by decide), h26], fun y _ _ _ a _ _ _ _ _ _ => g4 y a, fun y _ _ _ => by rw [g5],
      by rw [g6]; exact hT, fun z hz => by rw [g6]; exact hm0 z hz, g7, g8⟩
  | succ kk ih =>
    intro i l s hik hL hpc hh h10 h22 h3 h29 h26 h27 h28 hT hm0
    have hi : i < n := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      di_head Q off q hE s hpc hh (by rw [h10, h22]; exact_mod_cast hi)
    set s1 := run Q s detTape 4 with hs1
    have hLJ : (ddJ x i (i + 1) (n - (i + 1)) l).length ≤ Lm := by
      have := (ddI_length x n kk (i + 1) (ddJ x i (i + 1) (n - (i + 1)) l)).1
      simp only [ddI] at hL; omega
    obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ :=
      dj_loop Q off q hE hd1 n i Lm hi x m0 hx Db hDb (n - (i + 1)) (i + 1) l s1 (by omega) hLJ g1 g2
        (by rw [g3, h10]; push_cast; ring) (by rw [g5 22 (by decide) (by decide), h22])
        (by rw [g5 3 (by decide) (by decide), h3]) (by rw [g5 10 (by decide) (by decide), h10])
        (by rw [g5 29 (by decide) (by decide), h29])
        (by rw [g4, h29, h3]; push_cast; ring) (by rw [g5 26 (by decide) (by decide), h26])
        (by rw [g5 27 (by decide) (by decide), h27]) (by rw [g5 28 (by decide) (by decide), h28])
        (by rw [g7]; exact hT) (fun z hz => by rw [g7]; exact hm0 z hz)
    set s2 := run Q s1 detTape t2 with hs2
    have f2 : ∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 → y ≠ 31 → y ≠ 32 →
        s2.core.ptrs y = s.core.ptrs y :=
      fun y a b c e f g' h i' j' => by rw [p7 y a b c e f g' h i' j', g5 y c h]
    obtain ⟨T3, hT3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
      ih (i + 1) (ddJ x i (i + 1) (n - (i + 1)) l) s2 (by omega) (by simp only [ddI] at hL; exact hL)
        p1 p2 p3
        (by rw [f2 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), h22])
        (by rw [f2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), h3]) p4
        (by rw [f2 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), h26]) p5 p6 p9 p10
    refine ⟨4 + t2 + T3, by
        have h1 : (n - (i + 1)) * pairB d Lm ≤ n * pairB d Lm := Nat.mul_le_mul_right _ (by omega)
        have h2 : (kk + 1) * (n * pairB d Lm + 8) = kk * (n * pairB d Lm + 8) + n * pairB d Lm + 8 := by
          ring
        omega, ?_⟩
    have e2 : run Q s detTape (4 + t2) = s2 := by rw [run_add, ← hs1]
    rw [run_add, e2]
    exact ⟨q1, q2, q3, q4, q5, fun y a b c e f g' h i' j' l' => by
        rw [q6 y a b c e f g' h i' j' l', f2 y a b c f g' h i' j' l'],
      fun y a b c => by rw [q7 y a b c, p8 y a b c, g6], q8, q9, by rw [q10, p11, g8],
      by rw [q11, p12, g9]; ring⟩

/-- **The dedupe.** From `off + 67` with `top = Db ≥ 1 + n·d` and the points `x i` at
`1 + i·d`, `pre` reaches `off + 115` with the table of `ddList x n` at `Db`, `Dc = |ddList x n|`
in pointer `28` and `top = Db + |ddList x n|·d`. -/
lemma pre_dedup (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db)
    (s : State) (hpc : s.core.pc = off + 67) (hh : s.halted = false)
    (h22 : s.core.ptrs 22 = n) (h3 : s.core.ptrs 3 = d) (h23 : s.core.ptrs 23 = Db)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, s.core.mem ((1 + i' * d + c : ℕ) : ℤ) = x i' c) :
    ∃ t, t ≤ n * (n * pairB d (n * n) + 8) + 7 ∧ (run Q s detTape t).core.pc = off + 115 ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 23 = Db + (((ddList x n).length * d : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 28 = (ddList x n).length ∧
      (run Q s detTape t).core.ptrs 26 = Db ∧
      (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 23 → y ≠ 26 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 →
        y ≠ 31 → y ≠ 32 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      TableAt (run Q s detTape t).core.mem Db (ddList x n) ∧
      (∀ z, z < Db → (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ := dd_init Q off q hE s hpc hh
  set s1 := run Q s detTape 5 with hs1
  have hx' : ∀ i' : ℕ, i' < n → ∀ c : Fin d, s.core.mem ((1 + i' * d + c : ℕ) : ℤ) = x i' c := hx
  obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
    di_loop Q off q hE hd1 n (n * n) x s.core.mem hx' Db hDb n 0 [] s1 (by omega)
      (ddList_length x n) g1 g2 g3
      (by rw [g8 22 (by decide) (by decide) (by decide) (by decide) (by decide), h22])
      (by rw [g8 3 (by decide) (by decide) (by decide) (by decide) (by decide), h3])
      (by rw [g7]; simp) (by rw [g4, h23]) (by rw [g5, h23]; simp) (by rw [g6]; simp)
      (fun m v hv => by simp at hv) (fun z _ => by rw [g10])
  refine ⟨5 + t2, by omega, ?_⟩
  rw [run_add, ← hs1]
  exact ⟨p1, p2, p3, p4, p5, fun y a b c e f g' h i' j' l' m' => by
      rw [p6 y a b c e g' h i' j' l' m', g8 y a f g' h i'],
    fun y a b c => by rw [p7 y a b c, g9], p8, fun z hz => by rw [p9 z hz], by rw [p10, g11],
    by rw [p11, g12]; ring⟩

end DetANN.Supplement.Thm32

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

theorem _root_.solution :
    ∀ {d : ℕ} (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db)
    (s : State) (hpc : s.core.pc = off + 67) (hh : s.halted = false)
    (h22 : s.core.ptrs 22 = n) (h3 : s.core.ptrs 3 = d) (h23 : s.core.ptrs 23 = Db)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, s.core.mem ((1 + i' * d + c : ℕ) : ℤ) = x i' c),
    ∃ t, t ≤ n * (n * pairB d (n * n) + 8) + 7 ∧ (run Q s detTape t).core.pc = off + 115 ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 23 = Db + (((ddList x n).length * d : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 28 = (ddList x n).length ∧
      (run Q s detTape t).core.ptrs 26 = Db ∧
      (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 23 → y ≠ 26 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 →
        y ≠ 31 → y ≠ 32 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      TableAt (run Q s detTape t).core.mem Db (ddList x n) ∧
      (∀ z, z < Db → (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t :=
  DetANN.Supplement.Thm32.pre_dedup

end DetANN.Supplement.Thm32

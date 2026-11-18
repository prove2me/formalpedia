-- Prove2me | solution 1 for DetANN.HPIM.BB.walk_steps
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T14:18:18.298662+00:00
-- url     : https://prove2.me/submissions/19c7f1be-4645-4789-b843-24ab73ddd250

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

-- ===== BB_SegA =====
namespace DetANN.HPIM.BB.SA

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.BB DetANN.HPIM.PP DetANN.HPIM.QP

/-- Offsets 0–14: constants, `N := 0`, `cur := root`, `top := −1`. -/
lemma seg_setup (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) :
    (run Q s detTape 15).core.pc = off + 15 ∧ (run Q s detTape 15).halted = false ∧
      Consts (run Q s detTape 15) (s.core.ptrs 13) ∧ (run Q s detTape 15).core.ptrs 41 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 17 ∧ (run Q s detTape 15).core.ptrs 43 = -1 ∧
      (∀ x < 40, (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 15).core.regs = s.core.regs ∧ (run Q s detTape 15).core.mem = s.core.mem ∧
      (run Q s detTape 15).integerMemory = s.integerMemory ∧
      (run Q s detTape 15).work = s.work + 15 ∧ cellsWritten Q s 15 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢; subst hh
  rw [show pc = off + 0 from hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, ?_, by simp, by simp, by simp, ?_, rfl, rfl, rfl, rfl, by simp⟩
  · refine ⟨by simp, by simp, by simp; ring, by simp; ring, by simp; ring, by simp; ring, by simp,
      by simp⟩
  · intro x hx
    simp (disch := omega) only [Function.update_apply, if_neg]

/-- Offsets 15–25 at a leaf: record `n₀` := (kind `0`, address `u`), `N := n₀ + 1`, to `POP`. -/
lemma seg_leaf (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (n0 : ℕ) (s : State)
    (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u)
    (h41 : s.core.ptrs 41 = n0) (hu : A ≤ u) (hk : s.integerMemory u = 0) :
    (run Q s detTape 11).core.pc = off + 34 ∧ (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧
      (run Q s detTape 11).integerMemory (fa A 0 n0) = 0 ∧
      (run Q s detTape 11).integerMemory (fa A 1 n0) = u ∧
      (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 41 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 →
        (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      ∀ c ∈ cellsWritten Q s 11, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h42 h41 hk ⊢
  subst hh h42 c13
  rw [hpc]
  have hk' : im (ptrs 42) ≤ ptrs 69 := by rw [hk, c69]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell, Function.update_apply]
  simp (config := {decide := true}) only [if_false, if_true]
  rw [if_pos hk']
  rw [run_zero, cw_zero]
  unfold fa
  refine ⟨rfl, rfl, by simp [h41], ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]; exact hk
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro z z1 z2
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    rcases hc with h | h <;> subst h
    · right; congr 1; omega
    · left; congr 1; omega

/-- Offsets 15–33 at a cut: record `n₀` := (kind `1`, address `u`, link `tp`), push, to the left child. -/
lemma seg_cut (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tp : ℤ) (n0 : ℕ) (s : State)
    (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u)
    (h41 : s.core.ptrs 41 = n0) (h43 : s.core.ptrs 43 = tp) (hu : A ≤ u) (hk : s.integerMemory u = 1) :
    (run Q s detTape 19).core.pc = off + 15 ∧ (run Q s detTape 19).halted = false ∧
      (run Q s detTape 19).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧
      (run Q s detTape 19).core.ptrs 42 = s.integerMemory (u + 2) ∧
      (run Q s detTape 19).core.ptrs 43 = n0 ∧
      (run Q s detTape 19).integerMemory (fa A 0 n0) = 1 ∧
      (run Q s detTape 19).integerMemory (fa A 1 n0) = u ∧
      (run Q s detTape 19).integerMemory (fa A 4 n0) = tp ∧
      (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → z ≠ fa A 4 n0 →
        (run Q s detTape 19).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 41 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 →
        (run Q s detTape 19).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 19).core.regs = s.core.regs ∧ (run Q s detTape 19).core.mem = s.core.mem ∧
      (run Q s detTape 19).work = s.work + 19 ∧
      ∀ c ∈ cellsWritten Q s 19, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0) ∨ c = (false, fa A 4 n0) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h42 h41 h43 hk ⊢
  subst hh h42 c13 h43
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  unfold fa
  refine ⟨rfl, rfl, by simp [h41], ?_, by simp [h41], ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
    rw [show ptrs 42 + 1 + 1 = ptrs 42 + 2 by ring, if_pos trivial]
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]; exact hk
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro z z1 z2 z3
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5 x6 x7
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    rcases hc with h | h | h <;> subst h
    · right; left; congr 1; omega
    · left; congr 1; omega
    · right; right; congr 1; omega

/-- Offsets 34–47 with `top = k ≥ 0`: pop `k`, go to the right child of record `k`. -/
lemma seg_pop (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = k) :
    (run Q s detTape 14).core.pc = off + 15 ∧ (run Q s detTape 14).halted = false ∧
      (run Q s detTape 14).core.ptrs 42 = s.integerMemory (s.integerMemory (fa A 1 k) + 3) ∧
      (run Q s detTape 14).core.ptrs 43 = s.integerMemory (fa A 4 k) ∧
      (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 67 → x ≠ 71 →
        (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧
      (run Q s detTape 14).integerMemory = s.integerMemory ∧
      (run Q s detTape 14).work = s.work + 14 ∧ cellsWritten Q s 14 = ∅ := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h43 ⊢
  subst hh c13
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  unfold fa
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, by simp⟩
  · simp only [Function.update_apply]
    simp (config := {decide := true}) only [if_true, if_false]
    rw [show ptrs 61 - (ptrs 43 + ptrs 43 + (ptrs 43 + ptrs 43) + ptrs 43) = ptrs 13 - 5 + 1 - 5 * (k : ℤ)
      by omega]
    ring_nf
  · simp only [Function.update_apply]
    simp (config := {decide := true}) only [if_true, if_false]
    congr 1; omega
  · intro x x1 x2 x3 x4 x5
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- Offset 34 with `top = −1`: the walk is done. -/
lemma seg_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s : State)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = -1) :
    (run Q s detTape 1).core.pc = off + 48 ∧ (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core = { s.core with pc := off + 48 } ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅ := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h43 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, by simp⟩

/-- One backward step at a leaf record `k = i − 1`. -/
lemma sz_leaf (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State)
    (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 0) :
    (run Q s detTape 14).core.pc = off + 49 ∧ (run Q s detTape 14).halted = false ∧
      (run Q s detTape 14).core.ptrs 46 = (k : ℤ) ∧
      (run Q s detTape 14).integerMemory (fa A 2 k) = 1 ∧
      (run Q s detTape 14).integerMemory (fa A 3 k) = 0 ∧
      (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 →
        (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧
      (run Q s detTape 14).work = s.work + 14 ∧
      ∀ c ∈ cellsWritten Q s 14, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 hk ⊢
  subst hh c13
  unfold fa at hk
  have hk' : ∀ z, z = ptrs 13 - 5 + 0 - 5 * (k : ℤ) → im z = 0 := fun z hz => hz ▸ hk
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hk']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  unfold fa
  refine ⟨rfl, rfl, by simp; omega, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]; exact c69
  · intro z z1 z2
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5 x6 x7 x8
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    rcases hc with h | h <;> subst h
    · right; congr 1; omega
    · left; congr 1; omega

/-- One backward step at a cut record `k = i − 1`, with the sizes `a`, `b` of its children. -/
lemma sz_cut (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A a b : ℤ) (k : ℕ) (s : State)
    (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 1)
    (ha : s.integerMemory (fa A 2 (k + 1)) = a)
    (hb : s.integerMemory (A - 3 - 5 * ((k : ℤ) + 1 + a)) = b) :
    (run Q s detTape 29).core.pc = off + 49 ∧ (run Q s detTape 29).halted = false ∧
      (run Q s detTape 29).core.ptrs 46 = (k : ℤ) ∧
      (run Q s detTape 29).integerMemory (fa A 2 k) = 1 + a + b ∧
      (run Q s detTape 29).integerMemory (fa A 3 k) = 0 ∧
      (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 29).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 →
        (run Q s detTape 29).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 29).core.regs = s.core.regs ∧ (run Q s detTape 29).core.mem = s.core.mem ∧
      (run Q s detTape 29).work = s.work + 29 ∧
      ∀ c ∈ cellsWritten Q s 29, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 hk ha hb ⊢
  subst hh c13
  unfold fa at hk ha
  push_cast at ha
  have hk' : ∀ z, z = ptrs 13 - 5 + 0 - 5 * (k : ℤ) → im z = 1 := fun z hz => hz ▸ hk
  have ha' : ∀ z, z = ptrs 13 - 5 + 2 - 5 * ((k : ℤ) + 1) → im z = a := fun z hz => hz ▸ ha
  have hb' : ∀ z, z = ptrs 13 - 3 - 5 * ((k : ℤ) + 1 + a) → im z = b := fun z hz => hz ▸ hb
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hk']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  unfold fa
  refine ⟨rfl, rfl, by simp; omega, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, ha']
    simp (disch := omega) only [hb']
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]; exact c69
  · intro z z1 z2
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5 x6 x7 x8
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    rcases hc with h | h <;> subst h
    · right; congr 1; omega
    · left; congr 1; omega

/-- Offsets 78–86: frame base `A − 5N`, fuel `N + 1`, `j := 0`, output root := pointer `15`. -/
lemma seg_start (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (N : ℕ) (s : State)
    (hpc : s.core.pc = off + 78) (hh : s.halted = false) (hC : Consts s A) (h41 : s.core.ptrs 41 = N) :
    (run Q s detTape 9).core.pc = off + 87 ∧ (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 48 = A - 5 * (N : ℤ) ∧
      (run Q s detTape 9).core.ptrs 47 = A - 5 * (N : ℤ) ∧
      (run Q s detTape 9).core.ptrs 49 = ((N + 1 : ℕ) : ℤ) ∧
      (run Q s detTape 9).core.ptrs 50 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 9).core.ptrs 17 = s.core.ptrs 15 ∧
      (∀ x, x ≠ 17 → x ≠ 47 → x ≠ 48 → x ≠ 49 → x ≠ 50 → x ≠ 67 →
        (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅ := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h41 ⊢
  subst hh c13
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp; omega, by simp; omega, by simp; omega, by simp, by simp, ?_, rfl, rfl, rfl,
    rfl, by simp⟩
  intro x x1 x2 x3 x4 x5 x6
  simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- Offset 48: `i := N`. -/
lemma seg_dfsdone (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State)
    (hpc : s.core.pc = off + 48) (hh : s.halted = false) :
    (run Q s detTape 1).core.pc = off + 49 ∧ (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 46 = s.core.ptrs 41 ∧
      (∀ x, x ≠ 46 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x hx
  simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- `CALL` with fuel `0`: write the leaf `none` at `u`, then `RET`. -/
lemma seg_fuel0 (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (s : State)
    (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : s.core.ptrs 49 = 0)
    (h15 : s.core.ptrs 15 = u) :
    (run Q s detTape 10).core.pc = off + 218 ∧ (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 15 = u + 2 ∧
      (run Q s detTape 10).integerMemory u = 0 ∧ (run Q s detTape 10).integerMemory (u + 1) = 0 ∧
      (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape 10).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 56 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧
      (run Q s detTape 10).work = s.work + 10 ∧
      ∀ c ∈ cellsWritten Q s 10, c = (false, u) ∨ c = (false, u + 1) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h49 h15 ⊢
  subst hh c13 h15
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp; ring, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]; exact c69
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
  · intro z z1 z2
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    rcases hc with h | h <;> subst h
    · left; rfl
    · right; rfl

/-- `CALL` with fuel `≥ 1`: `S := sz[j]`, `i := j + S`, to `CNT`. -/
lemma seg_head (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (j : ℕ) (s : State)
    (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : 1 ≤ s.core.ptrs 49)
    (h50 : s.core.ptrs 50 = j) :
    (run Q s detTape 7).core.pc = off + 94 ∧ (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 51 = s.integerMemory (fa A 2 j) ∧
      (run Q s detTape 7).core.ptrs 46 = j + s.integerMemory (fa A 2 j) ∧
      (run Q s detTape 7).core.ptrs 67 = 5 * (j : ℤ) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 51 → x ≠ 67 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs = s.core.regs ∧ (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅ := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h49 h50 ⊢
  subst hh c13
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  unfold fa
  refine ⟨rfl, rfl, ?_, ?_, by simp; omega, ?_, rfl, rfl, rfl, rfl, by simp⟩
  · simp only [Function.update_apply]; simp (config := {decide := true}) only [if_true, if_false]
    congr 1; omega
  · simp only [Function.update_apply]; simp (config := {decide := true}) only [if_true, if_false]
    rw [h50]; congr 2; omega
  · intro x x1 x2 x3 x4
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- One count step at a leaf record `k` (`e` = 1 if unmarked, 0 if marked). -/
lemma cnt_leaf_seg (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e : ℤ) (k : ℕ)
    (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k)
    (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0))
    (hk : s.integerMemory (fa A 0 k) = 0) :
    ∃ t, t ≤ 16 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧
      (run Q s detTape t).integerMemory (fa A 4 k) = e ∧
      (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 →
        (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 h50 hm hk ⊢
  subst hh c13 h50
  unfold fa at hm hk ⊢
  have hk' : ∀ z, z = ptrs 13 - 5 + 0 - 5 * (k : ℤ) → im z = 0 := fun z hz => hz ▸ hk
  rw [hpc]
  have hm1 : im (ptrs 13 - 5 + 3 - 5 * (k : ℤ)) = 1 - e := by omega
  have hm' : ∀ x, x = ptrs 13 - 5 + 3 - 5 * (k : ℤ) → im x = 1 - e := fun x hx => hx ▸ hm1
  refine ⟨16, le_rfl, ?_⟩
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hm']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hk']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp; omega, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg]; ring
  · intro z z1
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5 x6 x7 x8
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    subst hc; congr 1; omega

/-- One count step at a cut record `k`: `cnt[k] := e + cnt[k+1] + cnt[k+1+sz[k+1]]`. -/
lemma cnt_cut_seg (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e a z b : ℤ) (k : ℕ)
    (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k)
    (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0))
    (hk : s.integerMemory (fa A 0 k) = 1) (ha : s.integerMemory (fa A 4 (k + 1)) = a)
    (hz : s.integerMemory (fa A 2 (k + 1)) = z) (hb : s.integerMemory (A - 1 - 5 * ((k : ℤ) + 1 + z)) = b) :
    ∃ t, t ≤ 33 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧
      (run Q s detTape t).integerMemory (fa A 4 k) = e + a + b ∧
      (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 →
        (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 h50 hm hk ha hz hb ⊢
  subst hh c13 h50
  unfold fa at hm hk ha hz ⊢
  push_cast at ha hz
  have hk' : ∀ x, x = ptrs 13 - 5 + 0 - 5 * (k : ℤ) → im x = 1 := fun x hx => hx ▸ hk
  have ha' : ∀ x, x = ptrs 13 - 5 + 4 - 5 * ((k : ℤ) + 1) → im x = a := fun x hx => hx ▸ ha
  have hz' : ∀ x, x = ptrs 13 - 5 + 2 - 5 * ((k : ℤ) + 1) → im x = z := fun x hx => hx ▸ hz
  have hb' : ∀ x, x = ptrs 13 - 1 - 5 * ((k : ℤ) + 1 + z) → im x = b := fun x hx => hx ▸ hb
  rw [hpc]
  have hm1 : im (ptrs 13 - 5 + 3 - 5 * (k : ℤ)) = 1 - e := by omega
  have hm' : ∀ x, x = ptrs 13 - 5 + 3 - 5 * (k : ℤ) → im x = 1 - e := fun x hx => hx ▸ hm1
  refine ⟨33, le_rfl, ?_⟩
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hm']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hk']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [ha', hz']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp; omega, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, ha', hz']
    simp (disch := omega) only [hb']
    ring
  · intro x x1
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5 x6 x7 x8
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    subst hc; congr 1; omega

theorem walk_steps' :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off) (hh : s.halted = false),
      (run Q s detTape 15).core.pc = off + 15 ∧ (run Q s detTape 15).halted = false ∧ Consts (run Q s detTape 15) (s.core.ptrs 13) ∧ (run Q s detTape 15).core.ptrs 41 = ((0 : ℕ) : ℤ) ∧ (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 17 ∧ (run Q s detTape 15).core.ptrs 43 = -1 ∧ (∀ x < 40, (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 15).core.regs = s.core.regs ∧ (run Q s detTape 15).core.mem = s.core.mem ∧ (run Q s detTape 15).integerMemory = s.integerMemory ∧ (run Q s detTape 15).work = s.work + 15 ∧ cellsWritten Q s 15 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (n0 : ℕ) (s : State) (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u) (h41 : s.core.ptrs 41 = n0) (hu : A ≤ u) (hk : s.integerMemory u = 0),
      (run Q s detTape 11).core.pc = off + 34 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧ (run Q s detTape 11).integerMemory (fa A 0 n0) = 0 ∧ (run Q s detTape 11).integerMemory (fa A 1 n0) = u ∧ (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 41 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).work = s.work + 11 ∧ ∀ c ∈ cellsWritten Q s 11, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tp : ℤ) (n0 : ℕ) (s : State) (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u) (h41 : s.core.ptrs 41 = n0) (h43 : s.core.ptrs 43 = tp) (hu : A ≤ u) (hk : s.integerMemory u = 1),
      (run Q s detTape 19).core.pc = off + 15 ∧ (run Q s detTape 19).halted = false ∧ (run Q s detTape 19).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧ (run Q s detTape 19).core.ptrs 42 = s.integerMemory (u + 2) ∧ (run Q s detTape 19).core.ptrs 43 = n0 ∧ (run Q s detTape 19).integerMemory (fa A 0 n0) = 1 ∧ (run Q s detTape 19).integerMemory (fa A 1 n0) = u ∧ (run Q s detTape 19).integerMemory (fa A 4 n0) = tp ∧ (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → z ≠ fa A 4 n0 → (run Q s detTape 19).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 41 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 → (run Q s detTape 19).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 19).core.regs = s.core.regs ∧ (run Q s detTape 19).core.mem = s.core.mem ∧ (run Q s detTape 19).work = s.work + 19 ∧ ∀ c ∈ cellsWritten Q s 19, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0) ∨ c = (false, fa A 4 n0)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = k),
      (run Q s detTape 14).core.pc = off + 15 ∧ (run Q s detTape 14).halted = false ∧ (run Q s detTape 14).core.ptrs 42 = s.integerMemory (s.integerMemory (fa A 1 k) + 3) ∧ (run Q s detTape 14).core.ptrs 43 = s.integerMemory (fa A 4 k) ∧ (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 67 → x ≠ 71 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).integerMemory = s.integerMemory ∧ (run Q s detTape 14).work = s.work + 14 ∧ cellsWritten Q s 14 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = -1),
      (run Q s detTape 1).core.pc = off + 48 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core = { s.core with pc := off + 48 } ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 0),
      (run Q s detTape 14).core.pc = off + 49 ∧ (run Q s detTape 14).halted = false ∧ (run Q s detTape 14).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape 14).integerMemory (fa A 2 k) = 1 ∧ (run Q s detTape 14).integerMemory (fa A 3 k) = 0 ∧ (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).work = s.work + 14 ∧ ∀ c ∈ cellsWritten Q s 14, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A a b : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 1) (ha : s.integerMemory (fa A 2 (k + 1)) = a) (hb : s.integerMemory (A - 3 - 5 * ((k : ℤ) + 1 + a)) = b),
      (run Q s detTape 29).core.pc = off + 49 ∧ (run Q s detTape 29).halted = false ∧ (run Q s detTape 29).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape 29).integerMemory (fa A 2 k) = 1 + a + b ∧ (run Q s detTape 29).integerMemory (fa A 3 k) = 0 ∧ (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 29).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 → (run Q s detTape 29).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 29).core.regs = s.core.regs ∧ (run Q s detTape 29).core.mem = s.core.mem ∧ (run Q s detTape 29).work = s.work + 29 ∧ ∀ c ∈ cellsWritten Q s 29, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (N : ℕ) (s : State) (hpc : s.core.pc = off + 78) (hh : s.halted = false) (hC : Consts s A) (h41 : s.core.ptrs 41 = N),
      (run Q s detTape 9).core.pc = off + 87 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 48 = A - 5 * (N : ℤ) ∧ (run Q s detTape 9).core.ptrs 47 = A - 5 * (N : ℤ) ∧ (run Q s detTape 9).core.ptrs 49 = ((N + 1 : ℕ) : ℤ) ∧ (run Q s detTape 9).core.ptrs 50 = ((0 : ℕ) : ℤ) ∧ (run Q s detTape 9).core.ptrs 17 = s.core.ptrs 15 ∧ (∀ x, x ≠ 17 → x ≠ 47 → x ≠ 48 → x ≠ 49 → x ≠ 50 → x ≠ 67 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off + 48) (hh : s.halted = false),
      (run Q s detTape 1).core.pc = off + 49 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs 46 = s.core.ptrs 41 ∧ (∀ x, x ≠ 46 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (s : State) (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : s.core.ptrs 49 = 0) (h15 : s.core.ptrs 15 = u),
      (run Q s detTape 10).core.pc = off + 218 ∧ (run Q s detTape 10).halted = false ∧ (run Q s detTape 10).core.ptrs 15 = u + 2 ∧ (run Q s detTape 10).integerMemory u = 0 ∧ (run Q s detTape 10).integerMemory (u + 1) = 0 ∧ (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape 10).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 56 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧ (run Q s detTape 10).work = s.work + 10 ∧ ∀ c ∈ cellsWritten Q s 10, c = (false, u) ∨ c = (false, u + 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : 1 ≤ s.core.ptrs 49) (h50 : s.core.ptrs 50 = j),
      (run Q s detTape 7).core.pc = off + 94 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 51 = s.integerMemory (fa A 2 j) ∧ (run Q s detTape 7).core.ptrs 46 = j + s.integerMemory (fa A 2 j) ∧ (run Q s detTape 7).core.ptrs 67 = 5 * (j : ℤ) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 51 → x ≠ 67 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs = s.core.regs ∧ (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k) (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0)) (hk : s.integerMemory (fa A 0 k) = 0),
      ∃ t, t ≤ 16 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape t).integerMemory (fa A 4 k) = e ∧ (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e a z b : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k) (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0)) (hk : s.integerMemory (fa A 0 k) = 1) (ha : s.integerMemory (fa A 4 (k + 1)) = a) (hz : s.integerMemory (fa A 2 (k + 1)) = z) (hb : s.integerMemory (A - 1 - 5 * ((k : ℤ) + 1 + z)) = b),
      ∃ t, t ≤ 33 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape t).integerMemory (fa A 4 k) = e + a + b ∧ (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k)) :=
  ⟨seg_setup, seg_leaf, seg_cut, seg_pop, seg_exit, sz_leaf, sz_cut, seg_start, seg_dfsdone, seg_fuel0, seg_head, cnt_leaf_seg, cnt_cut_seg⟩

end DetANN.HPIM.BB.SA

namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem _root_.solution :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off) (hh : s.halted = false),
      (run Q s detTape 15).core.pc = off + 15 ∧ (run Q s detTape 15).halted = false ∧ Consts (run Q s detTape 15) (s.core.ptrs 13) ∧ (run Q s detTape 15).core.ptrs 41 = ((0 : ℕ) : ℤ) ∧ (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 17 ∧ (run Q s detTape 15).core.ptrs 43 = -1 ∧ (∀ x < 40, (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 15).core.regs = s.core.regs ∧ (run Q s detTape 15).core.mem = s.core.mem ∧ (run Q s detTape 15).integerMemory = s.integerMemory ∧ (run Q s detTape 15).work = s.work + 15 ∧ cellsWritten Q s 15 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (n0 : ℕ) (s : State) (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u) (h41 : s.core.ptrs 41 = n0) (hu : A ≤ u) (hk : s.integerMemory u = 0),
      (run Q s detTape 11).core.pc = off + 34 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧ (run Q s detTape 11).integerMemory (fa A 0 n0) = 0 ∧ (run Q s detTape 11).integerMemory (fa A 1 n0) = u ∧ (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 41 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).work = s.work + 11 ∧ ∀ c ∈ cellsWritten Q s 11, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tp : ℤ) (n0 : ℕ) (s : State) (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u) (h41 : s.core.ptrs 41 = n0) (h43 : s.core.ptrs 43 = tp) (hu : A ≤ u) (hk : s.integerMemory u = 1),
      (run Q s detTape 19).core.pc = off + 15 ∧ (run Q s detTape 19).halted = false ∧ (run Q s detTape 19).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧ (run Q s detTape 19).core.ptrs 42 = s.integerMemory (u + 2) ∧ (run Q s detTape 19).core.ptrs 43 = n0 ∧ (run Q s detTape 19).integerMemory (fa A 0 n0) = 1 ∧ (run Q s detTape 19).integerMemory (fa A 1 n0) = u ∧ (run Q s detTape 19).integerMemory (fa A 4 n0) = tp ∧ (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → z ≠ fa A 4 n0 → (run Q s detTape 19).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 41 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 → (run Q s detTape 19).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 19).core.regs = s.core.regs ∧ (run Q s detTape 19).core.mem = s.core.mem ∧ (run Q s detTape 19).work = s.work + 19 ∧ ∀ c ∈ cellsWritten Q s 19, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0) ∨ c = (false, fa A 4 n0)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = k),
      (run Q s detTape 14).core.pc = off + 15 ∧ (run Q s detTape 14).halted = false ∧ (run Q s detTape 14).core.ptrs 42 = s.integerMemory (s.integerMemory (fa A 1 k) + 3) ∧ (run Q s detTape 14).core.ptrs 43 = s.integerMemory (fa A 4 k) ∧ (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 67 → x ≠ 71 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).integerMemory = s.integerMemory ∧ (run Q s detTape 14).work = s.work + 14 ∧ cellsWritten Q s 14 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = -1),
      (run Q s detTape 1).core.pc = off + 48 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core = { s.core with pc := off + 48 } ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 0),
      (run Q s detTape 14).core.pc = off + 49 ∧ (run Q s detTape 14).halted = false ∧ (run Q s detTape 14).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape 14).integerMemory (fa A 2 k) = 1 ∧ (run Q s detTape 14).integerMemory (fa A 3 k) = 0 ∧ (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).work = s.work + 14 ∧ ∀ c ∈ cellsWritten Q s 14, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A a b : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 1) (ha : s.integerMemory (fa A 2 (k + 1)) = a) (hb : s.integerMemory (A - 3 - 5 * ((k : ℤ) + 1 + a)) = b),
      (run Q s detTape 29).core.pc = off + 49 ∧ (run Q s detTape 29).halted = false ∧ (run Q s detTape 29).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape 29).integerMemory (fa A 2 k) = 1 + a + b ∧ (run Q s detTape 29).integerMemory (fa A 3 k) = 0 ∧ (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 29).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 → (run Q s detTape 29).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 29).core.regs = s.core.regs ∧ (run Q s detTape 29).core.mem = s.core.mem ∧ (run Q s detTape 29).work = s.work + 29 ∧ ∀ c ∈ cellsWritten Q s 29, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (N : ℕ) (s : State) (hpc : s.core.pc = off + 78) (hh : s.halted = false) (hC : Consts s A) (h41 : s.core.ptrs 41 = N),
      (run Q s detTape 9).core.pc = off + 87 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 48 = A - 5 * (N : ℤ) ∧ (run Q s detTape 9).core.ptrs 47 = A - 5 * (N : ℤ) ∧ (run Q s detTape 9).core.ptrs 49 = ((N + 1 : ℕ) : ℤ) ∧ (run Q s detTape 9).core.ptrs 50 = ((0 : ℕ) : ℤ) ∧ (run Q s detTape 9).core.ptrs 17 = s.core.ptrs 15 ∧ (∀ x, x ≠ 17 → x ≠ 47 → x ≠ 48 → x ≠ 49 → x ≠ 50 → x ≠ 67 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off + 48) (hh : s.halted = false),
      (run Q s detTape 1).core.pc = off + 49 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs 46 = s.core.ptrs 41 ∧ (∀ x, x ≠ 46 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (s : State) (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : s.core.ptrs 49 = 0) (h15 : s.core.ptrs 15 = u),
      (run Q s detTape 10).core.pc = off + 218 ∧ (run Q s detTape 10).halted = false ∧ (run Q s detTape 10).core.ptrs 15 = u + 2 ∧ (run Q s detTape 10).integerMemory u = 0 ∧ (run Q s detTape 10).integerMemory (u + 1) = 0 ∧ (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape 10).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 56 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧ (run Q s detTape 10).work = s.work + 10 ∧ ∀ c ∈ cellsWritten Q s 10, c = (false, u) ∨ c = (false, u + 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : 1 ≤ s.core.ptrs 49) (h50 : s.core.ptrs 50 = j),
      (run Q s detTape 7).core.pc = off + 94 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 51 = s.integerMemory (fa A 2 j) ∧ (run Q s detTape 7).core.ptrs 46 = j + s.integerMemory (fa A 2 j) ∧ (run Q s detTape 7).core.ptrs 67 = 5 * (j : ℤ) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 51 → x ≠ 67 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs = s.core.regs ∧ (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k) (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0)) (hk : s.integerMemory (fa A 0 k) = 0),
      ∃ t, t ≤ 16 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape t).integerMemory (fa A 4 k) = e ∧ (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e a z b : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k) (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0)) (hk : s.integerMemory (fa A 0 k) = 1) (ha : s.integerMemory (fa A 4 (k + 1)) = a) (hz : s.integerMemory (fa A 2 (k + 1)) = z) (hb : s.integerMemory (A - 1 - 5 * ((k : ℤ) + 1 + z)) = b),
      ∃ t, t ≤ 33 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape t).integerMemory (fa A 4 k) = e + a + b ∧ (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k)) :=
  DetANN.HPIM.BB.SA.walk_steps'

end DetANN.HPIM.BB

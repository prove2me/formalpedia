-- Prove2me | solution 1 for DetANN.HPIM.BB.node_steps
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T14:18:19.256376+00:00
-- url     : https://prove2.me/submissions/0717c9dd-6475-4cac-92be-0c63b0a785b5

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

-- ===== BB_SegB =====
namespace DetANN.HPIM.BB.SB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.BB DetANN.HPIM.PP DetANN.HPIM.QP

/-- `total ≤ 1`: write the leaf with answer cell `av` at `u`, then `RET`. -/
lemma seg_leafout (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tot av : ℤ) (j : ℕ)
    (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A)
    (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h15 : s.core.ptrs 15 = u) (htot : s.integerMemory (fa A 4 j) = tot)
    (htl : tot ≤ 1) (hu : A ≤ u)
    (hav : (s.integerMemory (fa A 0 j) = 0 ∧ s.integerMemory (s.integerMemory (fa A 1 j) + 2) = av) ∨
      (s.integerMemory (fa A 0 j) = 1 ∧ av = 0)) :
    ∃ t, t ≤ 20 ∧ (run Q s detTape t).core.pc = off + 218 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 15 = u + 2 ∧
      (run Q s detTape t).integerMemory u = 0 ∧ (run Q s detTape t).integerMemory (u + 1) = av ∧
      (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 45 → x ≠ 52 → x ≠ 56 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, u) ∨ c = (false, u + 1) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h67 h15 htot hav ⊢
  subst hh c13 h15
  unfold fa at htot hav
  have ht' : ∀ x, x = ptrs 13 - 5 + 4 - 5 * (j : ℤ) → im x = tot := fun x hx => hx ▸ htot
  rw [hpc]
  rcases hav with ⟨hk, ha⟩ | ⟨hk, rfl⟩
  · have hk' : ∀ x, x = ptrs 13 - 5 + 0 - 5 * (j : ℤ) → im x = 0 := fun x hx => hx ▸ hk
    have ha' : ∀ x, x = im (ptrs 13 - 5 + 1 - 5 * (j : ℤ)) + 2 → im x = av := fun x hx => hx ▸ ha
    have hq : ∀ x, x = ptrs 13 - 5 + 1 - 5 * (j : ℤ) → im x = im (ptrs 13 - 5 + 1 - 5 * (j : ℤ)) :=
      fun x hx => hx ▸ rfl
    refine ⟨20, le_rfl, ?_⟩
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    simp (disch := omega) only [ht']
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    simp (disch := omega) only [hk']
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    simp (disch := omega) only [hq]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    simp (disch := omega) only [ha']
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp; ring, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
    · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]; exact c69
    · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
    · intro z z1 z2
      simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
    · intro x x1 x2 x3 x4 x5
      simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
    · intro c hc
      simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
        Finset.mem_union, Finset.mem_singleton] at hc
      rcases hc with h | h <;> subst h
      · left; rfl
      · right; rfl
  · have hk' : ∀ x, x = ptrs 13 - 5 + 0 - 5 * (j : ℤ) → im x = 1 := fun x hx => hx ▸ hk
    refine ⟨16, by omega, ?_⟩
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    simp (disch := omega) only [ht']
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    simp (disch := omega) only [hk']
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, by simp; ring, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
    · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]; exact c69
    · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
    · intro z z1 z2
      simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
    · intro x x1 x2 x3 x4 x5
      simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
    · intro c hc
      simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
        Finset.mem_union, Finset.mem_singleton] at hc
      rcases hc with h | h <;> subst h
      · left; rfl
      · right; rfl

/-- `total ≥ 2`: `bs := total + 1`, `i := j`, `end := j + S`, to `SCAN`. -/
lemma seg_scan0 (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A tot : ℤ) (j : ℕ)
    (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A)
    (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h50 : s.core.ptrs 50 = j)
    (htot : s.integerMemory (fa A 4 j) = tot) (htl : 2 ≤ tot) :
    (run Q s detTape 8).core.pc = off + 135 ∧ (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 52 = tot ∧ (run Q s detTape 8).core.ptrs 54 = tot + 1 ∧
      (run Q s detTape 8).core.ptrs 46 = j ∧
      (run Q s detTape 8).core.ptrs 74 = j + s.core.ptrs 51 ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 52 → x ≠ 54 → x ≠ 56 → x ≠ 74 →
        (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅ := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h67 h50 htot ⊢
  subst hh c13
  unfold fa at htot
  have ht' : ∀ x, x = ptrs 13 - 5 + 4 - 5 * (j : ℤ) → im x = tot := fun x hx => hx ▸ htot
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [ht']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, by simp, by simp [h50], by simp [h50], ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x x1 x2 x3 x4 x5 x6
  simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- `SCAN` with `end ≤ i + 1`: the scan is done. -/
lemma scan_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A i e : ℤ) (s : State)
    (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = i) (h74 : s.core.ptrs 74 = e) (hie : e ≤ i + 1) :
    (run Q s detTape 2).core.pc = off + 153 ∧ (run Q s detTape 2).halted = false ∧
      (∀ x, x ≠ 46 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 h74 ⊢
  subst hh c13
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x x1
  simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- `SCAN` at a marked node `k = i + 1 < end`: skip. -/
lemma scan_marked (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e : ℤ) (k : ℕ) (s : State)
    (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e)
    (hm : s.integerMemory (fa A 3 k) = 1) :
    (run Q s detTape 9).core.pc = off + 135 ∧ (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 46 = k ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 72 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅ := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 h74 hm ⊢
  subst hh c13
  unfold fa at hm
  have hm' : ∀ x, x = ptrs 13 - 5 + 3 - 5 * (k : ℤ) → im x = 1 := fun x hx => hx ▸ hm
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hm']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp; omega, ?_, rfl, rfl, rfl, rfl, by simp⟩
  intro x x1 x2 x3 x4
  simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- `SCAN` at an unmarked node `k`: load its count into pointer `56` (offsets 135–145). -/
lemma scan_pre (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e ci : ℤ) (k : ℕ)
    (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e)
    (hm : s.integerMemory (fa A 3 k) = 0) (hci : s.integerMemory (fa A 4 k) = ci) :
    (run Q s detTape 10).core.pc = off + 146 ∧ (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 46 = k ∧ (run Q s detTape 10).core.ptrs 56 = ci ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 72 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧
      (run Q s detTape 10).integerMemory = s.integerMemory ∧
      (run Q s detTape 10).work = s.work + 10 ∧ cellsWritten Q s 10 = ∅ := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 h74 hm hci ⊢
  subst hh c13
  unfold fa at hm hci
  have hm' : ∀ x, x = ptrs 13 - 5 + 3 - 5 * (k : ℤ) → im x = 0 := fun x hx => hx ▸ hm
  have hc' : ∀ x, x = ptrs 13 - 5 + 4 - 5 * (k : ℤ) → im x = ci := fun x hx => hx ▸ hci
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hm']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp; omega, ?_, ?_, rfl, rfl, rfl, rfl, by simp⟩
  · simp (config := {decide := true}) only [Function.update_apply, if_true]
    exact hc' _ (by omega)
  · intro x x1 x2 x3 x4 x5
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- Offsets 146–152: score `max ci (tot − ci)`; take `k` if it beats `bs`. -/
lemma scan_post (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (tot ci : ℤ) (s : State)
    (hpc : s.core.pc = off + 146) (hh : s.halted = false) (h52 : s.core.ptrs 52 = tot)
    (h56 : s.core.ptrs 56 = ci) :
    ∃ t, t ≤ 7 ∧ (run Q s detTape t).core.pc = off + 135 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 54 =
        (if max ci (tot - ci) < s.core.ptrs 54 then max ci (tot - ci) else s.core.ptrs 54) ∧
      (run Q s detTape t).core.ptrs 53 =
        (if max ci (tot - ci) < s.core.ptrs 54 then s.core.ptrs 46 else s.core.ptrs 53) ∧
      (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 56 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h52 h56 ⊢
  subst hh h52 h56
  rw [hpc]
  by_cases h1 : ptrs 52 - ptrs 56 ≤ ptrs 56
  · rw [max_eq_left h1]
    by_cases h2 : ptrs 54 ≤ ptrs 56
    · refine ⟨3, by omega, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
      rw [run_zero, cw_zero]
      refine ⟨rfl, rfl, by simp <;> omega, by simp <;> omega, ?_, rfl, rfl, rfl, rfl, by simp⟩
      intro x x1 x2 x3 x4
      simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
    · refine ⟨6, by omega, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
      rw [run_zero, cw_zero]
      refine ⟨rfl, rfl, by simp <;> omega, by simp <;> omega, ?_, rfl, rfl, rfl, rfl, by simp⟩
      intro x x1 x2 x3 x4
      simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · rw [max_eq_right (by omega : ptrs 56 ≤ ptrs 52 - ptrs 56)]
    by_cases h2 : ptrs 54 ≤ ptrs 52 - ptrs 56
    · refine ⟨4, by omega, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
      rw [run_zero, cw_zero]
      refine ⟨rfl, rfl, by simp <;> omega, by simp <;> omega, ?_, rfl, rfl, rfl, rfl, by simp⟩
      intro x x1 x2 x3 x4
      simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
    · refine ⟨7, le_rfl, ?_⟩
      (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
      rw [run_zero, cw_zero]
      refine ⟨rfl, rfl, by simp <;> omega, by simp <;> omega, ?_, rfl, rfl, rfl, rfl, by simp⟩
      intro x x1 x2 x3 x4
      simp (disch := omega) only [Function.update_apply, if_pos, if_neg]

/-- Offsets 153–175: the test node at `u` (`I[u] = 1`, `I[u+1] = v`, `I[u+2] = u + 4`), then the box
source address of record `b`. -/
lemma seg_node1 (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u v a src : ℤ) (b : ℕ)
    (s : State) (hpc : s.core.pc = off + 153) (hh : s.halted = false) (hC : Consts s A)
    (h15 : s.core.ptrs 15 = u) (h16 : s.core.ptrs 16 = v) (h53 : s.core.ptrs 53 = b)
    (hA : A ≤ 0) (hu : 0 ≤ u) (ha : s.integerMemory (fa A 1 b) = a) (ha1 : a + 1 < 0)
    (hs : s.integerMemory (a + 1) = src) :
    (run Q s detTape 23).core.pc = off + 176 ∧ (run Q s detTape 23).halted = false ∧
      (run Q s detTape 23).core.ptrs 55 = u ∧ (run Q s detTape 23).core.ptrs 15 = u + 4 ∧
      (run Q s detTape 23).core.ptrs 44 = src ∧
      (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 1 + s.core.ptrs 1 ∧
      (run Q s detTape 23).core.ptrs 46 = 0 ∧
      (run Q s detTape 23).integerMemory u = 1 ∧ (run Q s detTape 23).integerMemory (u + 1) = v ∧
      (run Q s detTape 23).integerMemory (u + 2) = u + 4 ∧
      (∀ z, z ≠ u → z ≠ u + 1 → z ≠ u + 2 → (run Q s detTape 23).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 46 → x ≠ 55 → x ≠ 56 → x ≠ 57 → x ≠ 72 →
        (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 23).core.regs = s.core.regs ∧ (run Q s detTape 23).core.mem = s.core.mem ∧
      (run Q s detTape 23).work = s.work + 23 ∧
      ∀ c ∈ cellsWritten Q s 23, c = (false, u) ∨ c = (false, u + 1) ∨ c = (false, u + 2) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h15 h16 h53 ha hs ⊢
  subst hh c13 h15 h16
  unfold fa at ha
  have ha' : ∀ x, x = ptrs 13 - 5 + 1 - 5 * (b : ℤ) → im x = a := fun x hx => hx ▸ ha
  have hs' : ∀ x, x = a + 1 → im x = src := fun x hx => hx ▸ hs
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [ha']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [hs']
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, by simp; ring, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]; ring
  · intro z z1 z2 z3
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5 x6 x7
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    try simp only [or_assoc] at hc
    rcases hc with h | h | h <;> subst h <;> simp <;> omega

/-- One copy step (offsets 176–182). -/
lemma copy_step (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (q : ℤ) (s : State)
    (hpc : s.core.pc = off + 176) (hh : s.halted = false) (h46 : s.core.ptrs 46 = q)
    (hq : q < s.core.ptrs 57) :
    (run Q s detTape 7).core.pc = off + 176 ∧ (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 46 = q + 1 ∧
      (∀ x, x ≠ 46 → x ≠ 58 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 40 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem =
        Function.update s.core.mem (s.core.ptrs 16 + q) (s.core.mem (s.core.ptrs 44 + q)) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 16 + q) := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h46 hq ⊢
  subst hh h46
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro x x1 x2
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · first | rfl | (simp only [Function.update_apply]; simp (config := {decide := true}) only [if_true, if_false])
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    subst hc; simp

/-- Offsets 183–198: `v += 2m`; push the frame `(j, b, u, f)`; `f := f − 1`, `j := b`; `CALL`. -/
lemma seg_push (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (sp : ℤ) (s : State)
    (hpc : s.core.pc = off + 183) (hh : s.halted = false) (h47 : s.core.ptrs 47 = sp) :
    (run Q s detTape 16).core.pc = off + 87 ∧ (run Q s detTape 16).halted = false ∧
      (run Q s detTape 16).core.ptrs 16 = s.core.ptrs 16 + s.core.ptrs 57 ∧
      (run Q s detTape 16).core.ptrs 47 = sp - 4 ∧
      (run Q s detTape 16).core.ptrs 49 = s.core.ptrs 49 - 1 ∧
      (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 53 ∧
      (run Q s detTape 16).integerMemory (sp - 4) = s.core.ptrs 50 ∧
      (run Q s detTape 16).integerMemory (sp - 3) = s.core.ptrs 53 ∧
      (run Q s detTape 16).integerMemory (sp - 2) = s.core.ptrs 55 ∧
      (run Q s detTape 16).integerMemory (sp - 1) = s.core.ptrs 49 ∧
      (∀ z, (z < sp - 4 ∨ sp ≤ z) → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 16 → x ≠ 44 → x ≠ 47 → x ≠ 49 → x ≠ 50 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 16).core.regs = s.core.regs ∧ (run Q s detTape 16).core.mem = s.core.mem ∧
      (run Q s detTape 16).work = s.work + 16 ∧
      ∀ c ∈ cellsWritten Q s 16, c.1 = false ∧ sp - 4 ≤ c.2 ∧ c.2 < sp := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h47 ⊢
  subst hh h47
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, by simp; ring, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
  · intro z hz
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    try simp only [or_assoc] at hc
    rcases hc with h | h | h | h <;> subst h <;> simp <;> omega

/-- `RET` with a frame on the stack (offsets 218–243): pop `(j, b, u, f)`, `I[u+3] := ptr15`, set up
the marking of `[b, b + sz b)`. -/
lemma seg_ret (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A sp base j b u f Sb : ℤ)
    (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hC : Consts s A)
    (h47 : s.core.ptrs 47 = sp) (h48 : s.core.ptrs 48 = base) (hsp : sp < base) (hsp0 : sp + 4 ≤ 0)
    (hu : 0 ≤ u) (hA : A ≤ 0)
    (f0 : s.integerMemory sp = j) (f1 : s.integerMemory (sp + 1) = b)
    (f2 : s.integerMemory (sp + 2) = u) (f3 : s.integerMemory (sp + 3) = f)
    (hb : 0 ≤ b) (hSb : s.integerMemory (A - 3 - 5 * b) = Sb) :
    (run Q s detTape 26).core.pc = off + 244 ∧ (run Q s detTape 26).halted = false ∧
      (run Q s detTape 26).core.ptrs 50 = j ∧ (run Q s detTape 26).core.ptrs 53 = b ∧
      (run Q s detTape 26).core.ptrs 55 = u ∧ (run Q s detTape 26).core.ptrs 49 = f ∧
      (run Q s detTape 26).core.ptrs 47 = sp + 4 ∧ (run Q s detTape 26).core.ptrs 74 = b + Sb ∧
      (run Q s detTape 26).core.ptrs 46 = b ∧ (run Q s detTape 26).core.ptrs 56 = 1 ∧
      (run Q s detTape 26).integerMemory (u + 3) = s.core.ptrs 15 ∧
      (∀ z, z ≠ u + 3 → (run Q s detTape 26).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 51 → x ≠ 53 → x ≠ 55 → x ≠ 56 → x ≠ 72 →
        x ≠ 74 → (run Q s detTape 26).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 26).core.regs = s.core.regs ∧ (run Q s detTape 26).core.mem = s.core.mem ∧
      (run Q s detTape 26).work = s.work + 26 ∧
      ∀ c ∈ cellsWritten Q s 26, c = (false, u + 3) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h47 h48 f0 f1 f2 f3 hSb ⊢
  subst hh c13 h47 h48
  have e0 : ∀ x, x = ptrs 47 → im x = j := fun x hx => hx ▸ f0
  have e1 : ∀ x, x = ptrs 47 + 1 → im x = b := fun x hx => hx ▸ f1
  have e2 : ∀ x, x = ptrs 47 + 2 → im x = u := fun x hx => hx ▸ f2
  have e3 : ∀ x, x = ptrs 47 + 3 → im x = f := fun x hx => hx ▸ f3
  have e4 : ∀ x, x = ptrs 13 - 3 - 5 * b → im x = Sb := fun x hx => hx ▸ hSb
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [e0]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [e1]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [e2]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [e3]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  simp (disch := omega) only [e4]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  refine ⟨rfl, rfl, by simp, by simp, by simp, by simp, by simp; ring, by simp, by simp, by simp, ?_, ?_, ?_,
    rfl, rfl, rfl, ?_⟩
  · simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true]
  · intro z hz
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    subst hc; congr 1; ring

/-- One marking step (offsets 244–251): `mk[i] := 1`. -/
lemma mark_step (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (i : ℕ) (s : State)
    (hpc : s.core.pc = off + 244) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = i) (h56 : s.core.ptrs 56 = 1) (hie : (i : ℤ) < s.core.ptrs 74) :
    (run Q s detTape 8).core.pc = off + 244 ∧ (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 46 = ((i + 1 : ℕ) : ℤ) ∧
      (run Q s detTape 8).integerMemory = Function.update s.integerMemory (fa A 3 i) 1 ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 72 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).work = s.work + 8 ∧
      ∀ c ∈ cellsWritten Q s 8, c = (false, fa A 3 i) := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 h56 hie ⊢
  subst hh c13
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  unfold fa
  refine ⟨rfl, rfl, by simp; omega, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [h56, show ptrs 63 - (ptrs 46 + ptrs 46 + (ptrs 46 + ptrs 46) + ptrs 46) =
      ptrs 13 - 5 + 3 - 5 * (i : ℤ) by omega]
  · intro x x1 x2 x3
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  · intro c hc
    simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hc
    subst hc; congr 1; omega

/-- `RET` with an empty stack: the block ends. -/
lemma seg_end (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State)
    (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hsp : s.core.ptrs 48 ≤ s.core.ptrs 47) :
    (run Q s detTape 1).core.pc = off + 254 ∧ (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core = { s.core with pc := off + 254 } ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅ := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hsp ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, by simp⟩

theorem node_steps' :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tot av : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A) (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h15 : s.core.ptrs 15 = u) (htot : s.integerMemory (fa A 4 j) = tot) (htl : tot ≤ 1) (hu : A ≤ u) (hav : (s.integerMemory (fa A 0 j) = 0 ∧ s.integerMemory (s.integerMemory (fa A 1 j) + 2) = av) ∨ (s.integerMemory (fa A 0 j) = 1 ∧ av = 0)),
      ∃ t, t ≤ 20 ∧ (run Q s detTape t).core.pc = off + 218 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 15 = u + 2 ∧ (run Q s detTape t).integerMemory u = 0 ∧ (run Q s detTape t).integerMemory (u + 1) = av ∧ (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 45 → x ≠ 52 → x ≠ 56 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, u) ∨ c = (false, u + 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A tot : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A) (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h50 : s.core.ptrs 50 = j) (htot : s.integerMemory (fa A 4 j) = tot) (htl : 2 ≤ tot),
      (run Q s detTape 8).core.pc = off + 135 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 52 = tot ∧ (run Q s detTape 8).core.ptrs 54 = tot + 1 ∧ (run Q s detTape 8).core.ptrs 46 = j ∧ (run Q s detTape 8).core.ptrs 74 = j + s.core.ptrs 51 ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 52 → x ≠ 54 → x ≠ 56 → x ≠ 74 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).integerMemory = s.integerMemory ∧ (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A i e : ℤ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = i) (h74 : s.core.ptrs 74 = e) (hie : e ≤ i + 1),
      (run Q s detTape 2).core.pc = off + 153 ∧ (run Q s detTape 2).halted = false ∧ (∀ x, x ≠ 46 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e) (hm : s.integerMemory (fa A 3 k) = 1),
      (run Q s detTape 9).core.pc = off + 135 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 46 = k ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 72 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e ci : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e) (hm : s.integerMemory (fa A 3 k) = 0) (hci : s.integerMemory (fa A 4 k) = ci),
      (run Q s detTape 10).core.pc = off + 146 ∧ (run Q s detTape 10).halted = false ∧ (run Q s detTape 10).core.ptrs 46 = k ∧ (run Q s detTape 10).core.ptrs 56 = ci ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 72 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧ (run Q s detTape 10).integerMemory = s.integerMemory ∧ (run Q s detTape 10).work = s.work + 10 ∧ cellsWritten Q s 10 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (tot ci : ℤ) (s : State) (hpc : s.core.pc = off + 146) (hh : s.halted = false) (h52 : s.core.ptrs 52 = tot) (h56 : s.core.ptrs 56 = ci),
      ∃ t, t ≤ 7 ∧ (run Q s detTape t).core.pc = off + 135 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 54 = (if max ci (tot - ci) < s.core.ptrs 54 then max ci (tot - ci) else s.core.ptrs 54) ∧ (run Q s detTape t).core.ptrs 53 = (if max ci (tot - ci) < s.core.ptrs 54 then s.core.ptrs 46 else s.core.ptrs 53) ∧ (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 56 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u v a src : ℤ) (b : ℕ) (s : State) (hpc : s.core.pc = off + 153) (hh : s.halted = false) (hC : Consts s A) (h15 : s.core.ptrs 15 = u) (h16 : s.core.ptrs 16 = v) (h53 : s.core.ptrs 53 = b) (hA : A ≤ 0) (hu : 0 ≤ u) (ha : s.integerMemory (fa A 1 b) = a) (ha1 : a + 1 < 0) (hs : s.integerMemory (a + 1) = src),
      (run Q s detTape 23).core.pc = off + 176 ∧ (run Q s detTape 23).halted = false ∧ (run Q s detTape 23).core.ptrs 55 = u ∧ (run Q s detTape 23).core.ptrs 15 = u + 4 ∧ (run Q s detTape 23).core.ptrs 44 = src ∧ (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 1 + s.core.ptrs 1 ∧ (run Q s detTape 23).core.ptrs 46 = 0 ∧ (run Q s detTape 23).integerMemory u = 1 ∧ (run Q s detTape 23).integerMemory (u + 1) = v ∧ (run Q s detTape 23).integerMemory (u + 2) = u + 4 ∧ (∀ z, z ≠ u → z ≠ u + 1 → z ≠ u + 2 → (run Q s detTape 23).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 46 → x ≠ 55 → x ≠ 56 → x ≠ 57 → x ≠ 72 → (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 23).core.regs = s.core.regs ∧ (run Q s detTape 23).core.mem = s.core.mem ∧ (run Q s detTape 23).work = s.work + 23 ∧ ∀ c ∈ cellsWritten Q s 23, c = (false, u) ∨ c = (false, u + 1) ∨ c = (false, u + 2)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (q : ℤ) (s : State) (hpc : s.core.pc = off + 176) (hh : s.halted = false) (h46 : s.core.ptrs 46 = q) (hq : q < s.core.ptrs 57),
      (run Q s detTape 7).core.pc = off + 176 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 46 = q + 1 ∧ (∀ x, x ≠ 46 → x ≠ 58 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 40 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem = Function.update s.core.mem (s.core.ptrs 16 + q) (s.core.mem (s.core.ptrs 44 + q)) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 16 + q)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (sp : ℤ) (s : State) (hpc : s.core.pc = off + 183) (hh : s.halted = false) (h47 : s.core.ptrs 47 = sp),
      (run Q s detTape 16).core.pc = off + 87 ∧ (run Q s detTape 16).halted = false ∧ (run Q s detTape 16).core.ptrs 16 = s.core.ptrs 16 + s.core.ptrs 57 ∧ (run Q s detTape 16).core.ptrs 47 = sp - 4 ∧ (run Q s detTape 16).core.ptrs 49 = s.core.ptrs 49 - 1 ∧ (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 53 ∧ (run Q s detTape 16).integerMemory (sp - 4) = s.core.ptrs 50 ∧ (run Q s detTape 16).integerMemory (sp - 3) = s.core.ptrs 53 ∧ (run Q s detTape 16).integerMemory (sp - 2) = s.core.ptrs 55 ∧ (run Q s detTape 16).integerMemory (sp - 1) = s.core.ptrs 49 ∧ (∀ z, (z < sp - 4 ∨ sp ≤ z) → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 16 → x ≠ 44 → x ≠ 47 → x ≠ 49 → x ≠ 50 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 16).core.regs = s.core.regs ∧ (run Q s detTape 16).core.mem = s.core.mem ∧ (run Q s detTape 16).work = s.work + 16 ∧ ∀ c ∈ cellsWritten Q s 16, c.1 = false ∧ sp - 4 ≤ c.2 ∧ c.2 < sp) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A sp base j b u f Sb : ℤ) (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hC : Consts s A) (h47 : s.core.ptrs 47 = sp) (h48 : s.core.ptrs 48 = base) (hsp : sp < base) (hsp0 : sp + 4 ≤ 0) (hu : 0 ≤ u) (hA : A ≤ 0) (f0 : s.integerMemory sp = j) (f1 : s.integerMemory (sp + 1) = b) (f2 : s.integerMemory (sp + 2) = u) (f3 : s.integerMemory (sp + 3) = f) (hb : 0 ≤ b) (hSb : s.integerMemory (A - 3 - 5 * b) = Sb),
      (run Q s detTape 26).core.pc = off + 244 ∧ (run Q s detTape 26).halted = false ∧ (run Q s detTape 26).core.ptrs 50 = j ∧ (run Q s detTape 26).core.ptrs 53 = b ∧ (run Q s detTape 26).core.ptrs 55 = u ∧ (run Q s detTape 26).core.ptrs 49 = f ∧ (run Q s detTape 26).core.ptrs 47 = sp + 4 ∧ (run Q s detTape 26).core.ptrs 74 = b + Sb ∧ (run Q s detTape 26).core.ptrs 46 = b ∧ (run Q s detTape 26).core.ptrs 56 = 1 ∧ (run Q s detTape 26).integerMemory (u + 3) = s.core.ptrs 15 ∧ (∀ z, z ≠ u + 3 → (run Q s detTape 26).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 51 → x ≠ 53 → x ≠ 55 → x ≠ 56 → x ≠ 72 → x ≠ 74 → (run Q s detTape 26).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 26).core.regs = s.core.regs ∧ (run Q s detTape 26).core.mem = s.core.mem ∧ (run Q s detTape 26).work = s.work + 26 ∧ ∀ c ∈ cellsWritten Q s 26, c = (false, u + 3)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (i : ℕ) (s : State) (hpc : s.core.pc = off + 244) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = i) (h56 : s.core.ptrs 56 = 1) (hie : (i : ℤ) < s.core.ptrs 74),
      (run Q s detTape 8).core.pc = off + 244 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 46 = ((i + 1 : ℕ) : ℤ) ∧ (run Q s detTape 8).integerMemory = Function.update s.integerMemory (fa A 3 i) 1 ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 72 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).work = s.work + 8 ∧ ∀ c ∈ cellsWritten Q s 8, c = (false, fa A 3 i)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hsp : s.core.ptrs 48 ≤ s.core.ptrs 47),
      (run Q s detTape 1).core.pc = off + 254 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core = { s.core with pc := off + 254 } ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) :=
  ⟨seg_leafout, seg_scan0, scan_exit, scan_marked, scan_pre, scan_post, seg_node1, copy_step, seg_push, seg_ret, mark_step, seg_end⟩

end DetANN.HPIM.BB.SB

namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem _root_.solution :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tot av : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A) (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h15 : s.core.ptrs 15 = u) (htot : s.integerMemory (fa A 4 j) = tot) (htl : tot ≤ 1) (hu : A ≤ u) (hav : (s.integerMemory (fa A 0 j) = 0 ∧ s.integerMemory (s.integerMemory (fa A 1 j) + 2) = av) ∨ (s.integerMemory (fa A 0 j) = 1 ∧ av = 0)),
      ∃ t, t ≤ 20 ∧ (run Q s detTape t).core.pc = off + 218 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 15 = u + 2 ∧ (run Q s detTape t).integerMemory u = 0 ∧ (run Q s detTape t).integerMemory (u + 1) = av ∧ (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 45 → x ≠ 52 → x ≠ 56 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, u) ∨ c = (false, u + 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A tot : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A) (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h50 : s.core.ptrs 50 = j) (htot : s.integerMemory (fa A 4 j) = tot) (htl : 2 ≤ tot),
      (run Q s detTape 8).core.pc = off + 135 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 52 = tot ∧ (run Q s detTape 8).core.ptrs 54 = tot + 1 ∧ (run Q s detTape 8).core.ptrs 46 = j ∧ (run Q s detTape 8).core.ptrs 74 = j + s.core.ptrs 51 ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 52 → x ≠ 54 → x ≠ 56 → x ≠ 74 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).integerMemory = s.integerMemory ∧ (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A i e : ℤ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = i) (h74 : s.core.ptrs 74 = e) (hie : e ≤ i + 1),
      (run Q s detTape 2).core.pc = off + 153 ∧ (run Q s detTape 2).halted = false ∧ (∀ x, x ≠ 46 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e) (hm : s.integerMemory (fa A 3 k) = 1),
      (run Q s detTape 9).core.pc = off + 135 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 46 = k ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 72 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e ci : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e) (hm : s.integerMemory (fa A 3 k) = 0) (hci : s.integerMemory (fa A 4 k) = ci),
      (run Q s detTape 10).core.pc = off + 146 ∧ (run Q s detTape 10).halted = false ∧ (run Q s detTape 10).core.ptrs 46 = k ∧ (run Q s detTape 10).core.ptrs 56 = ci ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 72 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧ (run Q s detTape 10).integerMemory = s.integerMemory ∧ (run Q s detTape 10).work = s.work + 10 ∧ cellsWritten Q s 10 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (tot ci : ℤ) (s : State) (hpc : s.core.pc = off + 146) (hh : s.halted = false) (h52 : s.core.ptrs 52 = tot) (h56 : s.core.ptrs 56 = ci),
      ∃ t, t ≤ 7 ∧ (run Q s detTape t).core.pc = off + 135 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 54 = (if max ci (tot - ci) < s.core.ptrs 54 then max ci (tot - ci) else s.core.ptrs 54) ∧ (run Q s detTape t).core.ptrs 53 = (if max ci (tot - ci) < s.core.ptrs 54 then s.core.ptrs 46 else s.core.ptrs 53) ∧ (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 56 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u v a src : ℤ) (b : ℕ) (s : State) (hpc : s.core.pc = off + 153) (hh : s.halted = false) (hC : Consts s A) (h15 : s.core.ptrs 15 = u) (h16 : s.core.ptrs 16 = v) (h53 : s.core.ptrs 53 = b) (hA : A ≤ 0) (hu : 0 ≤ u) (ha : s.integerMemory (fa A 1 b) = a) (ha1 : a + 1 < 0) (hs : s.integerMemory (a + 1) = src),
      (run Q s detTape 23).core.pc = off + 176 ∧ (run Q s detTape 23).halted = false ∧ (run Q s detTape 23).core.ptrs 55 = u ∧ (run Q s detTape 23).core.ptrs 15 = u + 4 ∧ (run Q s detTape 23).core.ptrs 44 = src ∧ (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 1 + s.core.ptrs 1 ∧ (run Q s detTape 23).core.ptrs 46 = 0 ∧ (run Q s detTape 23).integerMemory u = 1 ∧ (run Q s detTape 23).integerMemory (u + 1) = v ∧ (run Q s detTape 23).integerMemory (u + 2) = u + 4 ∧ (∀ z, z ≠ u → z ≠ u + 1 → z ≠ u + 2 → (run Q s detTape 23).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 46 → x ≠ 55 → x ≠ 56 → x ≠ 57 → x ≠ 72 → (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 23).core.regs = s.core.regs ∧ (run Q s detTape 23).core.mem = s.core.mem ∧ (run Q s detTape 23).work = s.work + 23 ∧ ∀ c ∈ cellsWritten Q s 23, c = (false, u) ∨ c = (false, u + 1) ∨ c = (false, u + 2)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (q : ℤ) (s : State) (hpc : s.core.pc = off + 176) (hh : s.halted = false) (h46 : s.core.ptrs 46 = q) (hq : q < s.core.ptrs 57),
      (run Q s detTape 7).core.pc = off + 176 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 46 = q + 1 ∧ (∀ x, x ≠ 46 → x ≠ 58 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 40 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem = Function.update s.core.mem (s.core.ptrs 16 + q) (s.core.mem (s.core.ptrs 44 + q)) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 16 + q)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (sp : ℤ) (s : State) (hpc : s.core.pc = off + 183) (hh : s.halted = false) (h47 : s.core.ptrs 47 = sp),
      (run Q s detTape 16).core.pc = off + 87 ∧ (run Q s detTape 16).halted = false ∧ (run Q s detTape 16).core.ptrs 16 = s.core.ptrs 16 + s.core.ptrs 57 ∧ (run Q s detTape 16).core.ptrs 47 = sp - 4 ∧ (run Q s detTape 16).core.ptrs 49 = s.core.ptrs 49 - 1 ∧ (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 53 ∧ (run Q s detTape 16).integerMemory (sp - 4) = s.core.ptrs 50 ∧ (run Q s detTape 16).integerMemory (sp - 3) = s.core.ptrs 53 ∧ (run Q s detTape 16).integerMemory (sp - 2) = s.core.ptrs 55 ∧ (run Q s detTape 16).integerMemory (sp - 1) = s.core.ptrs 49 ∧ (∀ z, (z < sp - 4 ∨ sp ≤ z) → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 16 → x ≠ 44 → x ≠ 47 → x ≠ 49 → x ≠ 50 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 16).core.regs = s.core.regs ∧ (run Q s detTape 16).core.mem = s.core.mem ∧ (run Q s detTape 16).work = s.work + 16 ∧ ∀ c ∈ cellsWritten Q s 16, c.1 = false ∧ sp - 4 ≤ c.2 ∧ c.2 < sp) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A sp base j b u f Sb : ℤ) (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hC : Consts s A) (h47 : s.core.ptrs 47 = sp) (h48 : s.core.ptrs 48 = base) (hsp : sp < base) (hsp0 : sp + 4 ≤ 0) (hu : 0 ≤ u) (hA : A ≤ 0) (f0 : s.integerMemory sp = j) (f1 : s.integerMemory (sp + 1) = b) (f2 : s.integerMemory (sp + 2) = u) (f3 : s.integerMemory (sp + 3) = f) (hb : 0 ≤ b) (hSb : s.integerMemory (A - 3 - 5 * b) = Sb),
      (run Q s detTape 26).core.pc = off + 244 ∧ (run Q s detTape 26).halted = false ∧ (run Q s detTape 26).core.ptrs 50 = j ∧ (run Q s detTape 26).core.ptrs 53 = b ∧ (run Q s detTape 26).core.ptrs 55 = u ∧ (run Q s detTape 26).core.ptrs 49 = f ∧ (run Q s detTape 26).core.ptrs 47 = sp + 4 ∧ (run Q s detTape 26).core.ptrs 74 = b + Sb ∧ (run Q s detTape 26).core.ptrs 46 = b ∧ (run Q s detTape 26).core.ptrs 56 = 1 ∧ (run Q s detTape 26).integerMemory (u + 3) = s.core.ptrs 15 ∧ (∀ z, z ≠ u + 3 → (run Q s detTape 26).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 51 → x ≠ 53 → x ≠ 55 → x ≠ 56 → x ≠ 72 → x ≠ 74 → (run Q s detTape 26).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 26).core.regs = s.core.regs ∧ (run Q s detTape 26).core.mem = s.core.mem ∧ (run Q s detTape 26).work = s.work + 26 ∧ ∀ c ∈ cellsWritten Q s 26, c = (false, u + 3)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (i : ℕ) (s : State) (hpc : s.core.pc = off + 244) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = i) (h56 : s.core.ptrs 56 = 1) (hie : (i : ℤ) < s.core.ptrs 74),
      (run Q s detTape 8).core.pc = off + 244 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 46 = ((i + 1 : ℕ) : ℤ) ∧ (run Q s detTape 8).integerMemory = Function.update s.integerMemory (fa A 3 i) 1 ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 72 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).work = s.work + 8 ∧ ∀ c ∈ cellsWritten Q s 8, c = (false, fa A 3 i)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hsp : s.core.ptrs 48 ≤ s.core.ptrs 47),
      (run Q s detTape 1).core.pc = off + 254 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core = { s.core with pc := off + 254 } ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) :=
  DetANN.HPIM.BB.SB.node_steps'

end DetANN.HPIM.BB

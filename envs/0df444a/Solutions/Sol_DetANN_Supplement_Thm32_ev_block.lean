-- Prove2me | solution 1 for DetANN.Supplement.Thm32.ev_block
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-20T23:50:58.627183+00:00
-- url     : https://prove2.me/submissions/e5d9ece8-ff94-47b9-b040-2cbc29b157ff

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
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_SignedBlocks
import Theorems.Thm_DetANN_sylvester_hadamard

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

lemma len_evA (off : ℕ) : (evA off).length = 43 := rfl

lemma len_fw (off : ℕ) : (fw off).length = 23 := rfl

lemma emb_evA {Q : Program} {off : ℕ} (hE : Embeds Q (ev off) off) : Embeds Q (evA off) (off + 0) := by
  have h := embeds_app_left (embeds_app_left hE)
  simpa only [Nat.add_zero] using h

lemma emb_fw {Q : Program} {off : ℕ} (hE : Embeds Q (ev off) off) :
    Embeds Q (fw (off + 43)) (off + 43) := by
  have h := embeds_app_right (embeds_app_left hE)
  simpa only [len_evA] using h

lemma emb_evB {Q : Program} {off : ℕ} (hE : Embeds Q (ev off) off) : Embeds Q (evB off) (off + 66) := by
  have h := embeds_app_right hE
  simpa only [List.length_append, len_evA, len_fw, Nat.add_assoc, Nat.reduceAdd] using h

end DetANN.Supplement.Thm32

-- ===== T32_EvSeg =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- Constants; read `L` and `d`; start the stride table. -/
lemma ev_init (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (Lv dv : ℤ) (s : State)
    (hpc : s.core.pc = off + 0) (hh : s.halted = false)
    (fi0 : s.integerMemory (s.core.ptrs 0) = Lv)
    (fi1 : s.integerMemory (1) = dv) :
    (run Q s detTape 7).core.pc = off + 7 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 1 = 1 ∧
      (run Q s detTape 7).core.ptrs 2 = 2 ∧
      (run Q s detTape 7).core.ptrs 3 = dv ∧
      (run Q s detTape 7).core.ptrs 4 = 0 ∧
      (run Q s detTape 7).core.ptrs 6 = 2 ∧
      (run Q s detTape 7).core.ptrs 7 = 1 ∧
      (run Q s detTape 7).core.ptrs 14 = Lv ∧
      (∀ x, x ≠ 1 → x ≠ 2 → x ≠ 3 → x ≠ 4 → x ≠ 6 → x ≠ 7 → x ≠ 14 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs = s.core.regs ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fi0 fi1 ⊢
  subst hh
  have ei0 : ∀ z, z = ptrs 0 → im z = Lv := fun z hz => hz ▸ fi0
  have ei1 : ∀ z, z = 1 → im z = dv := fun z hz => hz ▸ fi1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0, ei1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0, ei1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Store one stride. -/
lemma st_step (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 7) (hh : s.halted = false)
    (hb0 : s.core.ptrs 7 < s.core.ptrs 3) :
    (run Q s detTape 6).core.pc = off + 7 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 4 = s.core.ptrs 4 + 1 ∧
      (run Q s detTape 6).core.ptrs 6 = s.core.ptrs 6 + 1 ∧
      (run Q s detTape 6).core.ptrs 7 = 2 * s.core.ptrs 7 ∧
      (∀ x, x ≠ 4 → x ≠ 6 → x ≠ 7 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory (s.core.ptrs 6) = s.core.ptrs 7 ∧
      (∀ z, z ≠ s.core.ptrs 6 → (run Q s detTape 6).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      ∀ c ∈ cellsWritten Q s 6, c = (false, s.core.ptrs 6) := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- Strides done; the scale `1/√(Ld)`; `Sb = -1-d`. -/
lemma st_exit (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 7) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 7) :
    (run Q s detTape 11).core.pc = off + 23 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 10 = 0 ∧
      (run Q s detTape 11).core.ptrs 13 = 0 ∧
      (run Q s detTape 11).core.ptrs 15 = -s.core.ptrs 3 - 1 ∧
      (∀ x, x ≠ 10 → x ≠ 13 → x ≠ 15 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs 0 = Real.sqrt ((((s.core.ptrs 14 : ℤ)) : ℝ) * (((s.core.ptrs 3 : ℤ)) : ℝ)) ∧
      (run Q s detTape 11).core.regs 1 = (1 : ℝ) ∧
      (run Q s detTape 11).core.regs 4 = ((1 : ℝ) / Real.sqrt ((((s.core.ptrs 14 : ℤ)) : ℝ) * (((s.core.ptrs 3 : ℤ)) : ℝ))) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 4 → (run Q s detTape 11).core.regs x = s.core.regs x) ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      cellsWritten Q s 11 = ∅ := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma ab_step (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 23) (hh : s.halted = false)
    (hb0 : s.core.ptrs 10 < s.core.ptrs 14) :
    (run Q s detTape 4).core.pc = off + 23 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 10 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 4).core.ptrs 13 = s.core.ptrs 13 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 10 → x ≠ 13 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Scratch base `fb = L·d`; start the outer loop. -/
lemma ab_exit (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 23) (hh : s.halted = false)
    (hb0 : s.core.ptrs 14 ≤ s.core.ptrs 10) :
    (run Q s detTape 3).core.pc = off + 29 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 16 = 0 ∧
      (run Q s detTape 3).core.ptrs 17 = 0 ∧
      (∀ x, x ≠ 16 → x ≠ 17 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma vl_exit (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 29) (hh : s.halted = false)
    (hb0 : s.core.ptrs 14 ≤ s.core.ptrs 16) :
    (run Q s detTape 1).core.pc = off + 79 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

lemma vl_head (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 29) (hh : s.halted = false)
    (hb0 : s.core.ptrs 16 < s.core.ptrs 14) :
    (run Q s detTape 2).core.pc = off + 31 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 18 = 0 ∧
      (∀ x, x ≠ 18 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- One signed coordinate into the scratch block. -/
lemma vr_step (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (sg zr : ℝ) (s : State)
    (hpc : s.core.pc = off + 31) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 15 - s.core.ptrs 17 - s.core.ptrs 18) = sg)
    (fr1 : s.core.mem (-s.core.ptrs 18 - 1) = zr)
    (hb0 : s.core.ptrs 18 < s.core.ptrs 3) :
    (run Q s detTape 12).core.pc = off + 31 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 11 = s.core.ptrs 13 + s.core.ptrs 18 ∧
      (run Q s detTape 12).core.ptrs 18 = s.core.ptrs 18 + 1 ∧
      (run Q s detTape 12).core.ptrs 19 = s.core.ptrs 17 + s.core.ptrs 18 ∧
      (∀ x, x ≠ 11 → x ≠ 18 → x ≠ 19 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs 0 = (sg * zr) ∧
      (run Q s detTape 12).core.regs 1 = zr ∧
      (∀ x, x ≠ 0 → x ≠ 1 → (run Q s detTape 12).core.regs x = s.core.regs x) ∧
      (run Q s detTape 12).core.mem (s.core.ptrs 13 + s.core.ptrs 18) = (sg * zr) ∧
      (∀ z, z ≠ s.core.ptrs 13 + s.core.ptrs 18 → (run Q s detTape 12).core.mem z = s.core.mem z) ∧
      (run Q s detTape 12).integerMemory = s.integerMemory ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      ∀ c ∈ cellsWritten Q s 12, c = (true, s.core.ptrs 13 + s.core.ptrs 18) := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 15 - ptrs 17 - ptrs 18 → mem z = sg := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = -ptrs 18 - 1 → mem z = zr := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma vr_exit (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 31) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 18) :
    (run Q s detTape 1).core.pc = off + 43 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_evA hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

lemma vj_init (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 66) (hh : s.halted = false) :
    (run Q s detTape 2).core.pc = off + 68 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 20 = 0 ∧
      (run Q s detTape 2).core.ptrs 21 = s.core.ptrs 16 ∧
      (∀ x, x ≠ 20 → x ≠ 21 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_evB hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- One scaled output. -/
lemma vj_step (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (v : ℝ) (s : State)
    (hpc : s.core.pc = off + 68) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 13 + s.core.ptrs 20) = v)
    (hb0 : s.core.ptrs 20 < s.core.ptrs 3) :
    (run Q s detTape 8).core.pc = off + 68 ∧
      (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 11 = s.core.ptrs 13 + s.core.ptrs 20 ∧
      (run Q s detTape 8).core.ptrs 20 = s.core.ptrs 20 + 1 ∧
      (run Q s detTape 8).core.ptrs 21 = s.core.ptrs 21 + s.core.ptrs 14 ∧
      (∀ x, x ≠ 11 → x ≠ 20 → x ≠ 21 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs 0 = (v * s.core.regs 4) ∧
      (∀ x, x ≠ 0 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧
      (run Q s detTape 8).core.mem (s.core.ptrs 21) = (v * s.core.regs 4) ∧
      (∀ z, z ≠ s.core.ptrs 21 → (run Q s detTape 8).core.mem z = s.core.mem z) ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧
      ∀ c ∈ cellsWritten Q s 8, c = (true, s.core.ptrs 21) := by
  have hS := emb_evB hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 13 + ptrs 20 → mem z = v := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

/-- Next repetition. -/
lemma vj_exit (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 68) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 20) :
    (run Q s detTape 4).core.pc = off + 29 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 16 = s.core.ptrs 16 + 1 ∧
      (run Q s detTape 4).core.ptrs 17 = s.core.ptrs 17 + s.core.ptrs 3 ∧
      (∀ x, x ≠ 16 → x ≠ 17 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs = s.core.regs ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_evB hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

end DetANN.Supplement.Thm32

-- ===== T32_FwSeg =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- Entry: the level counter starts at `cnt`. -/
lemma fw_entry (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (s : State)
    (hpc : s.core.pc = off + 0) (hh : s.halted = false) :
    (run Q s detTape 1).core.pc = off + 1 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 5 = s.core.ptrs 4 ∧
      (∀ x, x ≠ 5 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS : Embeds Q (fw off) (off + 0) := by simpa using hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh  ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- All levels done: exit. -/
lemma fw_done (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (s : State)
    (hpc : s.core.pc = off + 1) (hh : s.halted = false)
    (hb0 : s.core.ptrs 5 ≤ s.core.ptrs 0) :
    (run Q s detTape 1).core.pc = off + 23 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS : Embeds Q (fw off) (off + 0) := by simpa using hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Start a level: read its stride. -/
lemma fw_lvl (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (hv : ℤ) (s : State)
    (hpc : s.core.pc = off + 1) (hh : s.halted = false)
    (fi0 : s.integerMemory (s.core.ptrs 2 + s.core.ptrs 5 - 1) = hv)
    (hb0 : s.core.ptrs 0 < s.core.ptrs 5) :
    (run Q s detTape 6).core.pc = off + 7 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 5 = s.core.ptrs 5 - 1 ∧
      (run Q s detTape 6).core.ptrs 6 = s.core.ptrs 2 + s.core.ptrs 5 - 1 ∧
      (run Q s detTape 6).core.ptrs 7 = hv ∧
      (run Q s detTape 6).core.ptrs 8 = 2 * hv ∧
      (run Q s detTape 6).core.ptrs 9 = 0 ∧
      (∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS : Embeds Q (fw off) (off + 0) := by simpa using hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fi0 hb0 ⊢
  subst hh
  have ei0 : ∀ z, z = ptrs 2 + ptrs 5 - 1 → im z = hv := fun z hz => hz ▸ fi0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- All blocks of the level done. -/
lemma fs_done (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (s : State)
    (hpc : s.core.pc = off + 7) (hh : s.halted = false)
    (hb0 : s.core.ptrs 3 ≤ s.core.ptrs 9) :
    (run Q s detTape 1).core.pc = off + 1 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS : Embeds Q (fw off) (off + 0) := by simpa using hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Start a block. -/
lemma fs_head (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (s : State)
    (hpc : s.core.pc = off + 7) (hh : s.halted = false)
    (hb0 : s.core.ptrs 9 < s.core.ptrs 3) :
    (run Q s detTape 2).core.pc = off + 9 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 10 = 0 ∧
      (∀ x, x ≠ 10 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS : Embeds Q (fw off) (off + 0) := by simpa using hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Block done: next block. -/
lemma fi_done (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (s : State)
    (hpc : s.core.pc = off + 9) (hh : s.halted = false)
    (hb0 : s.core.ptrs 7 ≤ s.core.ptrs 10) :
    (run Q s detTape 3).core.pc = off + 7 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 9 = s.core.ptrs 9 + s.core.ptrs 8 ∧
      (∀ x, x ≠ 9 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS : Embeds Q (fw off) (off + 0) := by simpa using hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- One butterfly. -/
lemma fi_step (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (x y : ℝ) (s : State)
    (hpc : s.core.pc = off + 9) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10) = x)
    (fr1 : s.core.mem (s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 + s.core.ptrs 7) = y)
    (hb0 : s.core.ptrs 10 < s.core.ptrs 7)
    (hx0 : 1 ≤ s.core.ptrs 7) :
    (run Q s detTape 12).core.pc = off + 9 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 10 = s.core.ptrs 10 + 1 ∧
      (run Q s detTape 12).core.ptrs 11 = s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 ∧
      (run Q s detTape 12).core.ptrs 12 = s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 + s.core.ptrs 7 ∧
      (∀ x, x ≠ 10 → x ≠ 11 → x ≠ 12 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs 0 = x ∧
      (run Q s detTape 12).core.regs 1 = y ∧
      (run Q s detTape 12).core.regs 2 = (x + y) ∧
      (run Q s detTape 12).core.regs 3 = (x - y) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 → (run Q s detTape 12).core.regs x = s.core.regs x) ∧
      (run Q s detTape 12).core.mem (s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10) = (x + y) ∧
      (run Q s detTape 12).core.mem (s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 + s.core.ptrs 7) = (x - y) ∧
      (∀ z, z ≠ s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 → z ≠ s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 + s.core.ptrs 7 → (run Q s detTape 12).core.mem z = s.core.mem z) ∧
      (run Q s detTape 12).integerMemory = s.integerMemory ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      ∀ c ∈ cellsWritten Q s 12, c = (true, s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10) ∨ c = (true, s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 + s.core.ptrs 7) := by
  have hS : Embeds Q (fw off) (off + 0) := by simpa using hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 hx0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 13 + ptrs 9 + ptrs 10 → mem z = x := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 13 + ptrs 9 + ptrs 10 + ptrs 7 → mem z = y := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h <;> subst h <;> simp <;> omega)⟩

end DetANN.Supplement.Thm32

-- ===== T32_FwMath =====
namespace DetANN.Supplement.Thm32

open DetANN

/-- One butterfly level with stride `2^j` on `[0, n)`: the pair `(x, x + 2^j)` (bit `j` of `x`
clear) becomes `(f x + f (x + 2^j), f x - f (x + 2^j))`. -/
noncomputable def bfl (j n : ℕ) (f : ℕ → ℝ) : ℕ → ℝ := fun x =>
  if x < n then (if x / 2 ^ j % 2 = 1 then f (x - 2 ^ j) - f x else f x + f (x + 2 ^ j)) else f x

/-- Levels `k-1, k-2, …, 0`, top level first. -/
noncomputable def fwl : ℕ → ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, _, f => f
  | k + 1, n, f => fwl k n (bfl k n f)

lemma fwl_succ (k n : ℕ) (f : ℕ → ℝ) : fwl (k + 1) n f = fwl k n (bfl k n f) := rfl

lemma blk_le {m n c i : ℕ} (hd : m ∣ n) (hi : i < m) (h : c * m + i < n) : (c + 1) * m ≤ n := by
  obtain ⟨q, rfl⟩ := hd
  have hm : 0 < m := by omega
  have : c < q := by
    by_contra hc
    push Not at hc
    have : m * q ≤ c * m := by rw [mul_comm]; exact Nat.mul_le_mul_right m hc
    omega
  calc (c + 1) * m ≤ q * m := Nat.mul_le_mul_right m this
    _ = m * q := mul_comm _ _

lemma div_mod_lo (c k r : ℕ) (hr : r < 2 ^ k) : (2 * c * 2 ^ k + r) / 2 ^ k % 2 = 0 := by
  rw [show 2 * c * 2 ^ k + r = r + 2 ^ k * (2 * c) by ring, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt hr]
  omega

lemma div_mod_hi (c k r : ℕ) (hr : r < 2 ^ k) : ((2 * c + 1) * 2 ^ k + r) / 2 ^ k % 2 = 1 := by
  rw [show (2 * c + 1) * 2 ^ k + r = r + 2 ^ k * (2 * c + 1) by ring,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr]
  omega

/-- **FWHT correctness.** -/
theorem fwl_spec (k : ℕ) : ∀ (n : ℕ) (f : ℕ → ℝ) (c : ℕ) (i : Fin (2 ^ k)), 2 ^ k ∣ n →
    c * 2 ^ k + i < n →
    fwl k n f (c * 2 ^ k + i) = (sylvester k).mulVec (fun r => f (c * 2 ^ k + r)) i := by
  induction k with
  | zero =>
    intro n f c i _ _
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp at this; omega)
    subst hi
    simp [fwl, Matrix.mulVec, dotProduct, sylvester, bitDot]
  | succ k ih =>
    intro n f c i hd hlt
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hdk : 2 ^ k ∣ n := (pow_dvd_pow 2 (Nat.le_succ k)).trans hd
    have hblk := blk_le hd i.isLt hlt
    have hpk : 0 < 2 ^ k := by positivity
    have hcm : c * 2 ^ (k + 1) = 2 * c * 2 ^ k := by rw [hp]; ring
    have hiL : (i : ℕ) < 2 * 2 ^ k := lt_of_lt_of_eq i.isLt hp
    have hblk2 : 2 * c * 2 ^ k + 2 * 2 ^ k ≤ n := by
      have : (c + 1) * 2 ^ (k + 1) = 2 * c * 2 ^ k + 2 * 2 ^ k := by rw [hp]; ring
      omega
    rw [fwl_succ]
    set z : Fin (2 ^ (k + 1)) → ℝ := fun r => f (c * 2 ^ (k + 1) + r) with hz
    have hbt := (sylvester_hadamard k).2.2 z
    rcases Nat.lt_or_ge (i : ℕ) (2 ^ k) with hi | hi
    · -- lower half
      set i' : Fin (2 ^ k) := ⟨i, hi⟩
      have hii : i = loIdx k i' := Fin.ext rfl
      have e1 : c * 2 ^ (k + 1) + (i : ℕ) = 2 * c * 2 ^ k + (i' : ℕ) := by
        simp only [i']; rw [hcm]
      have hlt' : 2 * c * 2 ^ k + (i' : ℕ) < n := by rw [← e1]; exact hlt
      rw [e1, ih n _ (2 * c) i' hdk hlt', hii, (hbt i').1]
      congr 1
      funext r
      have hr := r.isLt
      have hx : 2 * c * 2 ^ k + (r : ℕ) < n := by omega
      simp only [bfl, if_pos hx, div_mod_lo c k r hr, zero_ne_one, if_false, hz, loIdx, hiIdx]
      rw [hcm, Nat.add_assoc, Nat.add_comm (r : ℕ) (2 ^ k)]
    · -- upper half
      have hi2 : (i : ℕ) - 2 ^ k < 2 ^ k := by omega
      set i' : Fin (2 ^ k) := ⟨i - 2 ^ k, hi2⟩
      have hii : i = hiIdx k i' := Fin.ext (by simp only [hiIdx, i']; omega)
      have e1 : c * 2 ^ (k + 1) + (i : ℕ) = (2 * c + 1) * 2 ^ k + (i' : ℕ) := by
        simp only [i']; rw [hcm]
        have : (2 * c + 1) * 2 ^ k = 2 * c * 2 ^ k + 2 ^ k := by ring
        omega
      have hlt' : (2 * c + 1) * 2 ^ k + (i' : ℕ) < n := by rw [← e1]; exact hlt
      rw [e1, ih n _ (2 * c + 1) i' hdk hlt', hii, (hbt i').2]
      congr 1
      funext r
      have hr := r.isLt
      have h21 : (2 * c + 1) * 2 ^ k = 2 * c * 2 ^ k + 2 ^ k := by ring
      have hx : (2 * c + 1) * 2 ^ k + (r : ℕ) < n := by omega
      simp only [bfl, if_pos hx, div_mod_hi c k r hr, if_true, hz, loIdx, hiIdx]
      have e2 : (2 * c + 1) * 2 ^ k + (r : ℕ) - 2 ^ k = c * 2 ^ (k + 1) + r := by
        rw [hcm]; omega
      rw [e2, hcm, h21, Nat.add_assoc]

/-- The whole array `[0, 2^k)`. -/
theorem fwl_full (k : ℕ) (f : ℕ → ℝ) (i : Fin (2 ^ k)) :
    fwl k (2 ^ k) f i = (sylvester k).mulVec (fun r => f r) i := by
  have := fwl_spec k (2 ^ k) f 0 i dvd_rfl (by simp)
  simpa using this

end DetANN.Supplement.Thm32

-- ===== T32_FwLoop =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- The lower index of the butterfly pair of `x` at stride `2^j`. -/
def plo (j x : ℕ) : ℕ := if x / 2 ^ j % 2 = 1 then x - 2 ^ j else x

/-- Level `j` done on the pairs with lower index `< lim`. -/
noncomputable def plv (j n : ℕ) (g : ℕ → ℝ) (lim : ℕ) : ℕ → ℝ := fun x =>
  if plo j x < lim then bfl j n g x else g x

lemma pow_le_of_odd {j x : ℕ} (h : x / 2 ^ j % 2 = 1) : 2 ^ j ≤ x := by
  by_contra hc
  push Not at hc
  rw [Nat.div_eq_of_lt hc] at h
  omega

lemma plo_le (j x : ℕ) : plo j x ≤ x := by
  unfold plo; split_ifs
  · exact Nat.sub_le _ _
  · exact le_rfl

lemma plo_even (j x : ℕ) : plo j x / 2 ^ j % 2 = 0 := by
  unfold plo
  split_ifs with h
  · have h2 := pow_le_of_odd h
    have e : (x - 2 ^ j) / 2 ^ j = x / 2 ^ j - 1 := by
      have := Nat.sub_mul_div x (2 ^ j) 1
      simpa using this
    rw [e]
    generalize x / 2 ^ j = q at h ⊢
    omega
  · generalize x / 2 ^ j = q at h ⊢
    omega

lemma hi_div {j lo : ℕ} (h : lo / 2 ^ j % 2 = 0) : (lo + 2 ^ j) / 2 ^ j % 2 = 1 := by
  rw [Nat.add_div_right _ (by positivity)]
  generalize lo / 2 ^ j = q at h ⊢
  omega

lemma plo_lo {j lo : ℕ} (h : lo / 2 ^ j % 2 = 0) : plo j lo = lo := by simp [plo, h]

lemma plo_hi {j lo : ℕ} (h : lo / 2 ^ j % 2 = 0) : plo j (lo + 2 ^ j) = lo := by
  unfold plo; rw [if_pos (hi_div h)]; simp

lemma plo_eq {j lo x : ℕ} (h : lo / 2 ^ j % 2 = 0) (e : plo j x = lo) : x = lo ∨ x = lo + 2 ^ j := by
  unfold plo at e
  split_ifs at e with hx
  · have := pow_le_of_odd hx
    right; omega
  · left; exact e

lemma plv_zero (j n : ℕ) (g : ℕ → ℝ) : plv j n g 0 = g := by
  funext x; simp [plv]

lemma plv_read_lo {j n lo : ℕ} (g : ℕ → ℝ) (h : lo / 2 ^ j % 2 = 0) : plv j n g lo lo = g lo := by
  simp [plv, plo_lo h]

lemma plv_read_hi {j n lo : ℕ} (g : ℕ → ℝ) (h : lo / 2 ^ j % 2 = 0) :
    plv j n g lo (lo + 2 ^ j) = g (lo + 2 ^ j) := by
  simp [plv, plo_hi h]

lemma plv_succ_lo {j n lo : ℕ} (g : ℕ → ℝ) (h : lo / 2 ^ j % 2 = 0) (hn : lo + 2 ^ j < n) :
    plv j n g (lo + 1) lo = g lo + g (lo + 2 ^ j) := by
  have h1 : lo < n := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hn
  simp [plv, plo_lo h, bfl, h1, h]

lemma plv_succ_hi {j n lo : ℕ} (g : ℕ → ℝ) (h : lo / 2 ^ j % 2 = 0) (hn : lo + 2 ^ j < n) :
    plv j n g (lo + 1) (lo + 2 ^ j) = g lo - g (lo + 2 ^ j) := by
  have h3 := hi_div h
  simp only [plv, plo_hi h, bfl, hn, h3, lt_add_one, if_true, Nat.add_sub_cancel]

lemma plv_succ_other {j n lo : ℕ} (g : ℕ → ℝ) (h : lo / 2 ^ j % 2 = 0) (x : ℕ) (h1 : x ≠ lo)
    (h2 : x ≠ lo + 2 ^ j) : plv j n g (lo + 1) x = plv j n g lo x := by
  have : plo j x ≠ lo := fun e => by rcases plo_eq h e with e | e <;> contradiction
  unfold plv
  by_cases hx : plo j x < lo
  · rw [if_pos hx, if_pos (by omega)]
  · rw [if_neg hx, if_neg (by omega)]

lemma plv_skip {j n c S H : ℕ} (g : ℕ → ℝ) (hH : H = 2 ^ j) (hS : S = 2 * c * H) :
    plv j n g (S + H) = plv j n g (S + 2 * H) := by
  funext x
  unfold plv
  have hp : 0 < H := by rw [hH]; positivity
  have key : ¬ (S + H ≤ plo j x ∧ plo j x < S + 2 * H) := by
    rintro ⟨h1, h2⟩
    have e : plo j x / 2 ^ j = 2 * c + 1 := by
      rw [← hH]
      apply Nat.div_eq_of_lt_le
      · rw [hS] at h1; nlinarith
      · rw [hS] at h2; nlinarith
    have := plo_even j x
    rw [e] at this
    omega
  by_cases h1 : plo j x < S + H
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

lemma plv_full {j n lim : ℕ} (g : ℕ → ℝ) (hn : n ≤ lim) (x : ℕ) (hx : x < n) :
    plv j n g lim x = bfl j n g x := by
  have := plo_le j x
  simp [plv, show plo j x < lim by omega]

lemma lo_even {j c i S H : ℕ} (hH : H = 2 ^ j) (hS : S = 2 * c * H) (hi : i < H) :
    (S + i) / 2 ^ j % 2 = 0 := by
  rw [hS, hH]; exact div_mod_lo c j i (by rw [← hH]; exact hi)

lemma fi_loop (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (j n c S H : ℕ)
    (hH : H = 2 ^ j) (hS : S = 2 * c * H) (g : ℕ → ℝ) (b : ℤ) (m0 : ℤ → ℝ) :
    ∀ (kk i : ℕ) (s : State), i + kk = H → s.core.pc = off + 9 → s.halted = false →
      s.core.ptrs 7 = H → s.core.ptrs 13 = b → s.core.ptrs 9 = S → s.core.ptrs 10 = i →
      s.core.ptrs 8 = 2 * H → S + 2 * H ≤ n →
      (∀ x : ℕ, x < n → s.core.mem (b + x) = plv j n g (S + i) x) →
      (∀ z, (z < b ∨ b + n ≤ z) → s.core.mem z = m0 z) →
      ∃ t, t ≤ 12 * kk + 3 ∧ (run Q s detTape t).core.pc = off + 7 ∧
        (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 9 = S + 2 * H ∧
        (∀ x, x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (∀ x : ℕ, x < n → (run Q s detTape t).core.mem (b + x) = plv j n g (S + 2 * H) x) ∧
        (∀ z, (z < b ∨ b + n ≤ z) → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ cc ∈ cellsWritten Q s t, cc.1 = true ∧ b ≤ cc.2 ∧ cc.2 < b + n := by
  have hp : 0 < H := by rw [hH]; positivity
  intro kk
  induction kk with
  | zero =>
    intro i s hik hpc hh h7 h13 h9 h10 h8 hSn hm hout
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
      fi_done Q off hE s hpc hh (by rw [h7, h10]; omega)
    refine ⟨3, by omega, g1, g2, by rw [g3, h9, h8], fun x a1 _ _ _ => g4 x a1, ?_,
      ?_, fun z hz => by rw [g6]; exact hout z hz, g7, g8, by rw [g9]; simp⟩
    · intro x _ _ _ _; rw [g5]
    · intro x hx; rw [g6, hm x hx, ← plv_skip g hH hS]; congr 1; omega
  | succ kk ih =>
    intro i s hik hpc hh h7 h13 h9 h10 h8 hSn hm hout
    have hi : i < H := by omega
    have hev := lo_even hH hS hi
    have hlt : S + i + H < n := by omega
    have hlt' : S + i + 2 ^ j < n := by rw [← hH]; exact hlt
    have rlo := plv_read_lo (n := n) g hev
    have rhi := plv_read_hi (n := n) g hev
    rw [← hH] at rhi
    have slo := plv_succ_lo g hev hlt'
    rw [← hH] at slo
    have shi := plv_succ_hi g hev hlt'
    rw [← hH] at shi
    have soth : ∀ x, x ≠ S + i → x ≠ S + i + H → plv j n g (S + i + 1) x = plv j n g (S + i) x :=
      fun x h1 h2 => plv_succ_other g hev x h1 (by rw [← hH]; exact h2)
    have c0 : ((S + i : ℕ) : ℤ) < n := by exact_mod_cast (by omega : S + i < n)
    have c1 : ((S + i + H : ℕ) : ℤ) < n := by exact_mod_cast hlt
    have a0 : s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 = b + ((S + i : ℕ) : ℤ) := by
      rw [h13, h9, h10]; push_cast; ring
    have a1 : s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 + s.core.ptrs 7 =
        b + ((S + i + H : ℕ) : ℤ) := by
      rw [h13, h9, h10, h7]; push_cast; ring
    have ex : s.core.mem (s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10) = g (S + i) := by
      rw [a0, hm _ (by omega), rlo]
    have ey : s.core.mem (s.core.ptrs 13 + s.core.ptrs 9 + s.core.ptrs 10 + s.core.ptrs 7) =
        g (S + i + H) := by
      rw [a1, hm _ hlt, rhi]
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩ :=
      fi_step Q off hE _ _ s hpc hh ex ey (by rw [h7, h10]; exact_mod_cast hi)
        (by rw [h7]; exact_mod_cast hp)
    set s1 := run Q s detTape 12 with hs1
    rw [a1] at g13 g14 g17
    rw [a0] at g12 g14 g17
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (i + 1) s1 (by omega) g1 g2 (by rw [g6 7 (by decide) (by decide) (by decide), h7])
        (by rw [g6 13 (by decide) (by decide) (by decide), h13])
        (by rw [g6 9 (by decide) (by decide) (by decide), h9]) (by rw [g3, h10]; push_cast; ring)
        (by rw [g6 8 (by decide) (by decide) (by decide), h8]) hSn
        (by
          intro x hx
          rw [show S + (i + 1) = S + i + 1 by ring]
          by_cases e1 : x = S + i
          · subst e1; rw [g12, slo]
          · by_cases e2 : x = S + i + H
            · subst e2; rw [g13, shi]
            · rw [soth x e1 e2, g14 _ (by intro h; apply e1; exact_mod_cast (add_left_cancel h))
                (by intro h; apply e2; exact_mod_cast (add_left_cancel h)), hm x hx])
        (by
          intro z hz
          rw [g14 z (by intro h; subst h; rcases hz with hz | hz <;> omega)
            (by intro h; subst h; rcases hz with hz | hz <;> omega)]
          exact hout z hz)
    refine ⟨12 + t2, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, q3, fun x x1 x2 x3 x4 => by rw [q4 x x1 x2 x3 x4, g6 x x2 x3 x4],
      fun x x1 x2 x3 x4 => by rw [q5 x x1 x2 x3 x4, g11 x x1 x2 x3 x4], q6, q7, by rw [q8, g15],
      by rw [q9, g16]; ring, ?_⟩
    intro cc hc
    rcases Finset.mem_union.1 hc with hc | hc
    · rcases g17 cc hc with rfl | rfl
      · exact ⟨rfl, by omega, by omega⟩
      · exact ⟨rfl, by omega, by omega⟩
    · exact q10 cc hc

lemma fs_loop (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (j n H : ℕ) (hH : H = 2 ^ j)
    (g : ℕ → ℝ) (b : ℤ) (m0 : ℤ → ℝ) :
    ∀ (cc c S : ℕ) (s : State), S = 2 * c * H → S + 2 * H * cc = n → s.core.pc = off + 7 →
      s.halted = false → s.core.ptrs 7 = H → s.core.ptrs 13 = b → s.core.ptrs 9 = S →
      s.core.ptrs 8 = 2 * H → s.core.ptrs 3 = n →
      (∀ x : ℕ, x < n → s.core.mem (b + x) = plv j n g S x) →
      (∀ z, (z < b ∨ b + n ≤ z) → s.core.mem z = m0 z) →
      ∃ t, t ≤ (12 * H + 7) * cc + 1 ∧ (run Q s detTape t).core.pc = off + 1 ∧
        (run Q s detTape t).halted = false ∧
        (∀ x, x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (∀ x : ℕ, x < n → (run Q s detTape t).core.mem (b + x) = bfl j n g x) ∧
        (∀ z, (z < b ∨ b + n ≤ z) → (run Q s detTape t).core.mem z = m0 z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ cc ∈ cellsWritten Q s t, cc.1 = true ∧ b ≤ cc.2 ∧ cc.2 < b + n := by
  have hp : 0 < H := by rw [hH]; positivity
  intro cc
  induction cc with
  | zero =>
    intro c S s hS hSn hpc hh h7 h13 h9 h8 h3 hm hout
    have hSn' : S = n := by simpa using hSn
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      fs_done Q off hE s hpc hh (by rw [h3, h9, hSn'])
    refine ⟨1, by omega, g1, g2, fun x _ _ _ _ => by rw [g3], fun x _ _ _ _ => by rw [g4], ?_,
      fun z hz => by rw [g5]; exact hout z hz, g6, g7, by rw [g8]; simp⟩
    intro x hx
    rw [g5, hm x hx, plv_full g (by omega) x hx]
  | succ cc ih =>
    intro c S s hS hSn hpc hh h7 h13 h9 h8 h3 hm hout
    have hpos : 0 < 2 * H * (cc + 1) := by positivity
    have hlt : S < n := by omega
    have e2 : 2 * H * (cc + 1) = 2 * H * cc + 2 * H := by ring
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
      fs_head Q off hE s hpc hh (by rw [h3, h9]; exact_mod_cast hlt)
    set s1 := run Q s detTape 2 with hs1
    obtain ⟨t1, ht1, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ :=
      fi_loop Q off hE j n c S H hH hS g b m0 H 0 s1 (by omega) g1 g2
        (by rw [g4 7 (by decide), h7]) (by rw [g4 13 (by decide), h13])
        (by rw [g4 9 (by decide), h9]) (by rw [g3]; rfl) (by rw [g4 8 (by decide), h8])
        (by omega) (fun x hx => by rw [g6, hm x hx]; rfl) (fun z hz => by rw [g6]; exact hout z hz)
    set s2 := run Q s1 detTape t1 with hs2
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (c + 1) (S + 2 * H) s2 (by rw [hS]; ring) (by omega) p1 p2
        (by rw [p4 7 (by decide) (by decide) (by decide) (by decide), g4 7 (by decide), h7])
        (by rw [p4 13 (by decide) (by decide) (by decide) (by decide), g4 13 (by decide), h13])
        (by rw [p3]; push_cast; ring)
        (by rw [p4 8 (by decide) (by decide) (by decide) (by decide), g4 8 (by decide), h8])
        (by rw [p4 3 (by decide) (by decide) (by decide) (by decide), g4 3 (by decide), h3]) p6 p7
    refine ⟨2 + t1 + t2, ?_, ?_⟩
    · have : (12 * H + 7) * (cc + 1) = (12 * H + 7) * cc + 12 * H + 7 := by ring
      omega
    have e12 : run Q s detTape (2 + t1) = s2 := by rw [run_add, ← hs1]
    rw [run_add, e12, cellsWritten_add, cellsWritten_add, e12, ← hs1]
    refine ⟨q1, q2, fun x x1 x2 x3 x4 => by rw [q3 x x1 x2 x3 x4, p4 x x1 x2 x3 x4, g4 x x2],
      fun x x1 x2 x3 x4 => by rw [q4 x x1 x2 x3 x4, p5 x x1 x2 x3 x4, g5], q5, q6,
      by rw [q7, p8, g7], by rw [q8, p9, g8]; ring, ?_⟩
    intro c' hc
    rw [g9, Finset.empty_union] at hc
    rcases Finset.mem_union.1 hc with hc | hc
    · exact p10 c' hc
    · exact q9 c' hc

lemma fw_lvls (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (n : ℕ) (b : ℤ) (m0 : ℤ → ℝ) :
    ∀ (t : ℕ) (s : State) (g : ℕ → ℝ), s.core.pc = off + 1 → s.halted = false →
      s.core.ptrs 5 = t → s.core.ptrs 0 = 0 → s.core.ptrs 2 = 2 → s.core.ptrs 3 = n →
      s.core.ptrs 13 = b → (∀ u : ℕ, u < t → s.integerMemory (2 + (u : ℤ)) = 2 ^ u) →
      2 ^ t ∣ n →
      (∀ x : ℕ, x < n → s.core.mem (b + x) = g x) →
      (∀ z, (z < b ∨ b + n ≤ z) → s.core.mem z = m0 z) →
      ∃ T, T ≤ t * (10 * n + 8) + 1 ∧ (run Q s detTape T).core.pc = off + 23 ∧
        (run Q s detTape T).halted = false ∧
        (∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 →
          (run Q s detTape T).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 → (run Q s detTape T).core.regs x = s.core.regs x) ∧
        (∀ x : ℕ, x < n → (run Q s detTape T).core.mem (b + x) = fwl t n g x) ∧
        (∀ z, (z < b ∨ b + n ≤ z) → (run Q s detTape T).core.mem z = m0 z) ∧
        (run Q s detTape T).integerMemory = s.integerMemory ∧
        (run Q s detTape T).work = s.work + T ∧
        ∀ cc ∈ cellsWritten Q s T, cc.1 = true ∧ b ≤ cc.2 ∧ cc.2 < b + n := by
  intro t
  induction t with
  | zero =>
    intro s g hpc hh h5 h0 h2 h3 h13 hst hd hm hout
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := fw_done Q off hE s hpc hh (by rw [h5, h0]; rfl)
    refine ⟨1, by omega, g1, g2, fun x _ _ _ _ _ _ _ _ => by rw [g3], fun x _ _ _ _ => by rw [g4],
      fun x hx => by rw [g5, hm x hx]; rfl, fun z hz => by rw [g5]; exact hout z hz, g6, g7,
      by rw [g8]; simp⟩
  | succ t ih =>
    intro s g hpc hh h5 h0 h2 h3 h13 hst hd hm hout
    obtain ⟨q, hq⟩ := hd
    have hH : (2 : ℕ) ^ t ≥ 1 := Nat.one_le_two_pow
    have fi0 : s.integerMemory (s.core.ptrs 2 + s.core.ptrs 5 - 1) = ((2 ^ t : ℕ) : ℤ) := by
      rw [h2, h5, show (2 : ℤ) + ((t + 1 : ℕ) : ℤ) - 1 = 2 + (t : ℤ) by push_cast; ring,
        hst t (by omega)]
      push_cast; rfl
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ :=
      fw_lvl Q off hE _ s hpc hh fi0 (by rw [h0, h5]; push_cast; omega)
    set s1 := run Q s detTape 6 with hs1
    have hn : 0 + 2 * 2 ^ t * q = n := by rw [hq, pow_succ]; ring
    obtain ⟨t1, ht1, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ :=
      fs_loop Q off hE t n (2 ^ t) rfl g b m0 q 0 0 s1 (by ring) hn g1 g2 g5
        (by rw [g8 13 (by decide) (by decide) (by decide) (by decide) (by decide), h13])
        (by rw [g7]; simp) (by simp [g6])
        (by rw [g8 3 (by decide) (by decide) (by decide) (by decide) (by decide), h3])
        (fun x hx => by rw [plv_zero, g10, hm x hx]) (fun z hz => by rw [g10]; exact hout z hz)
    set s2 := run Q s1 detTape t1 with hs2
    have fr : ∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 →
        s2.core.ptrs x = s.core.ptrs x := fun x x5 x6 x7 x8 x9 x10 x11 x12 => by
      rw [p3 x x9 x10 x11 x12, g8 x x5 x6 x7 x8 x9]
    obtain ⟨T2, hT2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih s2 (bfl t n g) p1 p2
        (by rw [p3 5 (by decide) (by decide) (by decide) (by decide), g3, h5]; push_cast; ring)
        (by rw [fr 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), h0])
        (by rw [fr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), h2])
        (by rw [fr 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), h3])
        (by rw [fr 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), h13])
        (fun u hu => by rw [p7, g11]; exact hst u (by omega))
        ⟨2 * q, by rw [hq, pow_succ]; ring⟩ p5 p6
    refine ⟨6 + t1 + T2, ?_, ?_⟩
    · have e1 : (12 * 2 ^ t + 7) * q ≤ 10 * n := by rw [hq, pow_succ]; nlinarith
      have e2 : (t + 1) * (10 * n + 8) = t * (10 * n + 8) + 10 * n + 8 := by ring
      omega
    have e12 : run Q s detTape (6 + t1) = s2 := by rw [run_add, ← hs1]
    rw [run_add, e12, cellsWritten_add, cellsWritten_add, e12, ← hs1]
    refine ⟨q1, q2, fun x x5 x6 x7 x8 x9 x10 x11 x12 => by
        rw [q3 x x5 x6 x7 x8 x9 x10 x11 x12, fr x x5 x6 x7 x8 x9 x10 x11 x12],
      fun x x1 x2 x3 x4 => by rw [q4 x x1 x2 x3 x4, p4 x x1 x2 x3 x4, g9], fun x hx => by
        rw [q5 x hx, fwl_succ], q6, by rw [q7, p7, g11], by rw [q8, p8, g12]; ring, ?_⟩
    intro c' hc
    rw [g13, Finset.empty_union] at hc
    rcases Finset.mem_union.1 hc with hc | hc
    · exact p9 c' hc
    · exact q9 c' hc

/-- **The FWHT block.** With `d = 2^k` in pointer `3`, `k` in pointer `4`, the strides `2^u`
(`u < k`) in integer cells `2 + u` and base `b` in pointer `13`, the block replaces the reals
`g 0, …, g (d-1)` at `b, …, b + d - 1` by `(sylvester k).mulVec g` and exits at `off + 23`. -/
theorem fw_spec (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (k : ℕ) (b : ℤ)
    (g : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 0) (hh : s.halted = false)
    (h4 : s.core.ptrs 4 = k) (h0 : s.core.ptrs 0 = 0) (h2 : s.core.ptrs 2 = 2)
    (h3 : s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ)) (h13 : s.core.ptrs 13 = b)
    (hst : ∀ u : ℕ, u < k → s.integerMemory (2 + (u : ℤ)) = 2 ^ u)
    (hm : ∀ x : ℕ, x < 2 ^ k → s.core.mem (b + x) = g x) :
    ∃ T, T ≤ k * (10 * 2 ^ k + 8) + 2 ∧ (run Q s detTape T).core.pc = off + 23 ∧
      (run Q s detTape T).halted = false ∧
      (∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 →
        (run Q s detTape T).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 → (run Q s detTape T).core.regs x = s.core.regs x) ∧
      (∀ i : Fin (2 ^ k), (run Q s detTape T).core.mem (b + (i : ℕ)) =
        (sylvester k).mulVec (fun r => g r) i) ∧
      (∀ z, (z < b ∨ b + ((2 ^ k : ℕ) : ℤ) ≤ z) → (run Q s detTape T).core.mem z = s.core.mem z) ∧
      (run Q s detTape T).integerMemory = s.integerMemory ∧
      (run Q s detTape T).work = s.work + T ∧
      ∀ cc ∈ cellsWritten Q s T, cc.1 = true ∧ b ≤ cc.2 ∧ cc.2 < b + ((2 ^ k : ℕ) : ℤ) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := fw_entry Q off hE s hpc hh
  set s1 := run Q s detTape 1 with hs1
  obtain ⟨T, hT, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    fw_lvls Q off hE (2 ^ k) b s.core.mem k s1 g g1 g2 (by rw [g3, h4])
      (by rw [g4 0 (by decide), h0]) (by rw [g4 2 (by decide), h2]) (by rw [g4 3 (by decide), h3])
      (by rw [g4 13 (by decide), h13]) (fun u hu => by rw [g7]; exact hst u hu) dvd_rfl
      (fun x hx => by rw [g6]; exact hm x hx) (fun z _ => by rw [g6])
  refine ⟨1 + T, by omega, ?_⟩
  rw [run_add, cellsWritten_add, ← hs1]
  refine ⟨q1, q2, fun x x5 x6 x7 x8 x9 x10 x11 x12 => by
      rw [q3 x x5 x6 x7 x8 x9 x10 x11 x12, g4 x x5], fun x x1 x2 x3 x4 => by rw [q4 x x1 x2 x3 x4, g5],
    fun i => by rw [q5 i i.isLt, fwl_full], q6, by rw [q7, g7], by rw [q8, g8]; ring, ?_⟩
  intro c' hc
  rw [g9, Finset.empty_union] at hc
  exact q9 c' hc

end DetANN.Supplement.Thm32

-- ===== T32_EvLoop =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma st_loop (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (k : ℕ) :
    ∀ (kk u : ℕ) (s : State), u + kk = k → s.core.pc = off + 7 → s.halted = false →
      s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ) → s.core.ptrs 7 = ((2 ^ u : ℕ) : ℤ) → s.core.ptrs 4 = u →
      s.core.ptrs 6 = 2 + (u : ℤ) → (∀ v : ℕ, v < u → s.integerMemory (2 + (v : ℤ)) = 2 ^ v) →
      ∃ t, t ≤ 6 * kk + 11 ∧ (run Q s detTape t).core.pc = off + 23 ∧
        (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 4 = k ∧
        (run Q s detTape t).core.ptrs 10 = 0 ∧ (run Q s detTape t).core.ptrs 13 = 0 ∧
        (run Q s detTape t).core.ptrs 15 = -s.core.ptrs 3 - 1 ∧
        (∀ x, x ≠ 4 → x ≠ 6 → x ≠ 7 → x ≠ 10 → x ≠ 13 → x ≠ 15 →
          (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs 4 =
          1 / Real.sqrt (((s.core.ptrs 14 : ℤ) : ℝ) * ((s.core.ptrs 3 : ℤ) : ℝ)) ∧
        (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 4 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (∀ v : ℕ, v < k → (run Q s detTape t).integerMemory (2 + (v : ℤ)) = 2 ^ v) ∧
        (∀ z, z < 2 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro u s huk hpc hh h3 h7 h4 h6 hst
    have hu : u = k := by omega
    subst hu
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ :=
      st_exit Q off hE s hpc hh (by rw [h3, h7])
    exact ⟨11, by omega, g1, g2, by rw [g6 4 (by decide) (by decide) (by decide), h4], g3, g4, g5,
      fun x x4 _ _ x10 x13 x15 => g6 x x10 x13 x15, g9, g10, g11, by rw [g12]; exact hst,
      fun z _ => by rw [g12], g13⟩
  | succ kk ih =>
    intro u s huk hpc hh h3 h7 h4 h6 hst
    have hlt : 2 ^ u < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
      st_step Q off hE s hpc hh (by rw [h3, h7]; exact_mod_cast hlt)
    set s1 := run Q s detTape 6 with hs1
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13⟩ :=
      ih (u + 1) s1 (by omega) g1 g2 (by rw [g6 3 (by decide) (by decide) (by decide), h3])
        (by rw [g5, h7]; push_cast; ring) (by rw [g3, h4]; push_cast; ring)
        (by rw [g4, h6]; push_cast; ring)
        (by
          intro v hv
          rcases Nat.lt_or_ge v u with h | h
          · rw [g10 _ (by rw [h6]; omega)]; exact hst v h
          · have : v = u := by omega
            subst this
            rw [← h6, g9, h7]; push_cast; rfl)
    refine ⟨6 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    refine ⟨q1, q2, q3, q4, q5, by rw [q6, g6 3 (by decide) (by decide) (by decide)],
      fun x x4 x6 x7 x10 x13 x15 => by rw [q7 x x4 x6 x7 x10 x13 x15, g6 x x4 x6 x7], ?_,
      fun x x0 x1 x4 => by rw [q9 x x0 x1 x4, g7], by rw [q10, g8], q11,
      fun z hz => by rw [q12 z hz, g10 z (by rw [h6]; omega)], by rw [q13, g11]; ring⟩
    rw [q8, g6 14 (by decide) (by decide) (by decide), g6 3 (by decide) (by decide) (by decide)]

lemma ab_loop (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (L d : ℕ) :
    ∀ (kk i : ℕ) (s : State), i + kk = L → s.core.pc = off + 23 → s.halted = false →
      s.core.ptrs 10 = i → s.core.ptrs 14 = L → s.core.ptrs 3 = d →
      s.core.ptrs 13 = ((i * d : ℕ) : ℤ) →
      ∃ t, t ≤ 4 * kk + 3 ∧ (run Q s detTape t).core.pc = off + 29 ∧
        (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 13 = ((L * d : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 16 = 0 ∧ (run Q s detTape t).core.ptrs 17 = 0 ∧
        (∀ x, x ≠ 10 → x ≠ 13 → x ≠ 16 → x ≠ 17 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro i s hik hpc hh h10 h14 h3 h13
    have hi : i = L := by omega
    subst hi
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      ab_exit Q off hE s hpc hh (by rw [h14, h10])
    exact ⟨3, by omega, g1, g2, by rw [g5 13 (by decide) (by decide), h13], g3, g4,
      fun x _ x13 x16 x17 => g5 x x16 x17, g6, g7, g8, g9⟩
  | succ kk ih =>
    intro i s hik hpc hh h10 h14 h3 h13
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
      ab_step Q off hE s hpc hh (by rw [h14, h10]; exact_mod_cast (by omega : i < L))
    set s1 := run Q s detTape 4 with hs1
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (i + 1) s1 (by omega) g1 g2 (by rw [g3, h10]; push_cast; ring)
        (by rw [g5 14 (by decide) (by decide), h14]) (by rw [g5 3 (by decide) (by decide), h3])
        (by rw [g4, h13, h3]; push_cast; ring)
    refine ⟨4 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, q3, q4, q5, fun x x10 x13 x16 x17 => by rw [q6 x x10 x13 x16 x17, g5 x x10 x13],
      by rw [q7, g6], by rw [q8, g7], by rw [q9, g8], by rw [q10, g9]; ring⟩

lemma vr_loop (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (d ib : ℕ) (fb : ℤ) (hfb : 0 ≤ fb)
    (σ z : ℕ → ℝ) (m0 : ℤ → ℝ) :
    ∀ (kk r : ℕ) (s : State), r + kk = d → s.core.pc = off + 31 → s.halted = false →
      s.core.ptrs 18 = r → s.core.ptrs 3 = d → s.core.ptrs 13 = fb → s.core.ptrs 15 = -(d : ℤ) - 1 →
      s.core.ptrs 17 = ib →
      (∀ r : ℕ, r < d → m0 (-(d : ℤ) - 1 - ib - r) = σ r) → (∀ r : ℕ, r < d → m0 (-(r : ℤ) - 1) = z r) →
      (∀ r' : ℕ, r' < r → s.core.mem (fb + r') = σ r' * z r') →
      (∀ y, (y < fb ∨ fb + r ≤ y) → s.core.mem y = m0 y) →
      ∃ t, t ≤ 12 * kk + 1 ∧ (run Q s detTape t).core.pc = off + 43 ∧
        (run Q s detTape t).halted = false ∧
        (∀ x, x ≠ 11 → x ≠ 18 → x ≠ 19 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 0 → x ≠ 1 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (∀ r' : ℕ, r' < d → (run Q s detTape t).core.mem (fb + r') = σ r' * z r') ∧
        (∀ y, (y < fb ∨ fb + d ≤ y) → (run Q s detTape t).core.mem y = m0 y) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro r s hrk hpc hh h18 h3 h13 h15 h17 hsg hz hm hout
    have hr : r = d := by omega
    subst hr
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ := vr_exit Q off hE s hpc hh (by rw [h3, h18])
    exact ⟨1, by omega, g1, g2, fun x _ _ _ => by rw [g3], fun x _ _ => by rw [g4],
      fun r' hr' => by rw [g5]; exact hm r' hr', fun y hy => by rw [g5]; exact hout y hy, g6, g7⟩
  | succ kk ih =>
    intro r s hrk hpc hh h18 h3 h13 h15 h17 hsg hz hm hout
    have hr : r < d := by omega
    have e0 : s.core.mem (s.core.ptrs 15 - s.core.ptrs 17 - s.core.ptrs 18) = σ r := by
      rw [h15, h17, h18, hout _ (Or.inl (by omega))]; exact hsg r hr
    have e1 : s.core.mem (-s.core.ptrs 18 - 1) = z r := by
      rw [h18, hout _ (Or.inl (by omega))]; exact hz r hr
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, _⟩ :=
      vr_step Q off hE _ _ s hpc hh e0 e1 (by rw [h18, h3]; exact_mod_cast hr)
    set s1 := run Q s detTape 12 with hs1
    rw [h13, h18] at g10 g11
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
      ih (r + 1) s1 (by omega) g1 g2 (by rw [g4, h18]; push_cast; ring)
        (by rw [g6 3 (by decide) (by decide) (by decide), h3])
        (by rw [g6 13 (by decide) (by decide) (by decide), h13])
        (by rw [g6 15 (by decide) (by decide) (by decide), h15])
        (by rw [g6 17 (by decide) (by decide) (by decide), h17]) hsg hz
        (by
          intro r' hr'
          rcases Nat.lt_or_ge r' r with h | h
          · rw [g11 _ (by omega)]; exact hm r' h
          · have : r' = r := by omega
            subst this; rw [g10])
        (by
          intro y hy
          rw [g11 _ (by push_cast at hy; omega)]
          exact hout y (by push_cast at hy; omega))
    refine ⟨12 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    exact ⟨q1, q2, fun x x11 x18 x19 => by rw [q3 x x11 x18 x19, g6 x x11 x18 x19],
      fun x x0 x1 => by rw [q4 x x0 x1, g9 x x0 x1], q5, q6, by rw [q7, g12], by rw [q8, g13]; ring⟩

lemma vj_loop (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (d L ℓ : ℕ) (fb : ℤ)
    (w : ℕ → ℝ) (sc : ℝ) (m0 : ℤ → ℝ) (hL : 0 < L) (hfar : ∀ j : ℕ, j < d → ((ℓ + j * L : ℕ) : ℤ) < fb) :
    ∀ (kk j : ℕ) (s : State), j + kk = d → s.core.pc = off + 68 → s.halted = false →
      s.core.ptrs 20 = j → s.core.ptrs 21 = ((ℓ + j * L : ℕ) : ℤ) → s.core.ptrs 3 = d →
      s.core.ptrs 13 = fb → s.core.ptrs 14 = L → s.core.regs 4 = sc →
      (∀ j' : ℕ, j' < d → s.core.mem (fb + j') = w j') →
      (∀ j' : ℕ, j' < j → s.core.mem ((ℓ + j' * L : ℕ) : ℤ) = w j' * sc) →
      (∀ y, (∀ j' : ℕ, j' < j → y ≠ ((ℓ + j' * L : ℕ) : ℤ)) → s.core.mem y = m0 y) →
      ∃ t, t ≤ 8 * kk + 4 ∧ (run Q s detTape t).core.pc = off + 29 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.ptrs 16 = s.core.ptrs 16 + 1 ∧
        (run Q s detTape t).core.ptrs 17 = s.core.ptrs 17 + d ∧
        (∀ x, x ≠ 11 → x ≠ 16 → x ≠ 17 → x ≠ 20 → x ≠ 21 →
          (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 0 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (∀ j' : ℕ, j' < d → (run Q s detTape t).core.mem ((ℓ + j' * L : ℕ) : ℤ) = w j' * sc) ∧
        (∀ y, (∀ j' : ℕ, j' < d → y ≠ ((ℓ + j' * L : ℕ) : ℤ)) → (run Q s detTape t).core.mem y = m0 y) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro j s hjk hpc hh h20 h21 h3 h13 h14 h4 hw hm hout
    have hj : j = d := by omega
    subst hj
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ := vj_exit Q off hE s hpc hh (by rw [h3, h20])
    exact ⟨4, by omega, g1, g2, g3, by rw [g4, h3],
      fun x _ x16 x17 _ _ => g5 x x16 x17, fun x _ => by rw [g6],
      fun j' hj' => by rw [g7]; exact hm j' hj', fun y hy => by rw [g7]; exact hout y hy, g8, g9⟩
  | succ kk ih =>
    intro j s hjk hpc hh h20 h21 h3 h13 h14 h4 hw hm hout
    have hj : j < d := by omega
    have e0 : s.core.mem (s.core.ptrs 13 + s.core.ptrs 20) = w j := by rw [h13, h20]; exact hw j hj
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, _⟩ :=
      vj_step Q off hE _ s hpc hh e0 (by rw [h20, h3]; exact_mod_cast hj)
    set s1 := run Q s detTape 8 with hs1
    rw [h21, h4] at g9
    rw [h21] at g10
    have inj : ∀ a b : ℕ, ((ℓ + a * L : ℕ) : ℤ) = ((ℓ + b * L : ℕ) : ℤ) → a = b := by
      intro a b hab
      have : ℓ + a * L = ℓ + b * L := by exact_mod_cast hab
      exact Nat.eq_of_mul_eq_mul_right hL (by omega)
    obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (j + 1) s1 (by omega) g1 g2 (by rw [g4, h20]; push_cast; ring)
        (by rw [g5, h21, h14]; push_cast; ring)
        (by rw [g6 3 (by decide) (by decide) (by decide), h3])
        (by rw [g6 13 (by decide) (by decide) (by decide), h13])
        (by rw [g6 14 (by decide) (by decide) (by decide), h14])
        (by rw [g8 4 (by decide), h4])
        (by
          intro j' hj'
          rw [g10 _ (by have := hfar j hj; omega)]; exact hw j' hj')
        (by
          intro j' hj'
          rcases Nat.lt_or_ge j' j with h | h
          · have e : ((ℓ + j' * L : ℕ) : ℤ) ≠ ((ℓ + j * L : ℕ) : ℤ) := fun e => by
              have := inj j' j e; omega
            rw [g10 _ e]; exact hm j' h
          · have : j' = j := by omega
            subst this; rw [g9])
        (by
          intro y hy
          rw [g10 _ (hy j (by omega))]
          exact hout y (fun j' hj' => hy j' (by omega)))
    refine ⟨8 + t2, by omega, ?_⟩
    rw [run_add, ← hs1]
    refine ⟨q1, q2, by rw [q3, g6 16 (by decide) (by decide) (by decide)],
      by rw [q4, g6 17 (by decide) (by decide) (by decide)],
      fun x x11 x16 x17 x20 x21 => by rw [q5 x x11 x16 x17 x20 x21, g6 x x11 x20 x21],
      fun x x0 => by rw [q6 x x0, g8 x x0], q7, q8, by rw [q9, g11], by rw [q10, g12]; ring⟩

end DetANN.Supplement.Thm32

-- ===== T32_EvMain =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- The transform of repetition `ℓ`: `(H_k (σ ℓ ⊙ z))_j`. -/
noncomputable def evW (k : ℕ) (σ : ℕ → ℕ → ℝ) (z : ℕ → ℝ) (ℓ : ℕ) : Fin (2 ^ k) → ℝ :=
  (sylvester k).mulVec (fun r => σ ℓ r * z r)

lemma ev_halt (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (s : State)
    (hpc : s.core.pc = off + 79) (hh : s.halted = false) :
    (run Q s detTape 1).halted = true ∧ (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).work = s.work + 1 := by
  have hS := emb_evB hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢
  subst hh
  rw [hpc, run_exec_seg hS rfl rfl rfl rfl]
  simp [exec, run_zero]

lemma cell_inj {L ℓ ℓ' j j' : ℕ} (h1 : ℓ < L) (h2 : ℓ' < L) (e : ℓ + j * L = ℓ' + j' * L) :
    ℓ = ℓ' := by
  have a1 : (ℓ + j * L) % L = ℓ := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
  have a2 : (ℓ' + j' * L) % L = ℓ' := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  rw [← a1, ← a2, e]

lemma cell_lt {ℓ L j d : ℕ} (h1 : ℓ < L) (h2 : j < d) : ℓ + j * L < L * d :=
  calc ℓ + j * L < L + j * L := by omega
    _ = (j + 1) * L := by ring
    _ ≤ d * L := Nat.mul_le_mul_right _ h2
    _ = L * d := mul_comm _ _

lemma vl_loop (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (k L : ℕ) (σ : ℕ → ℕ → ℝ)
    (z : ℕ → ℝ) (sc : ℝ) (m0 : ℤ → ℝ)
    (hsg : ∀ ℓ : ℕ, ℓ < L → ∀ r : ℕ, r < 2 ^ k →
      m0 (-((2 ^ k : ℕ) : ℤ) - 1 - ((ℓ * 2 ^ k : ℕ) : ℤ) - r) = σ ℓ r)
    (hz : ∀ r : ℕ, r < 2 ^ k → m0 (-(r : ℤ) - 1) = z r) :
    ∀ (kk ℓ : ℕ) (s : State), ℓ + kk = L → s.core.pc = off + 29 → s.halted = false →
      s.core.ptrs 16 = ℓ → s.core.ptrs 17 = ((ℓ * 2 ^ k : ℕ) : ℤ) →
      s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ) → s.core.ptrs 4 = k → s.core.ptrs 0 = 0 → s.core.ptrs 2 = 2 →
      s.core.ptrs 13 = ((L * 2 ^ k : ℕ) : ℤ) → s.core.ptrs 14 = L →
      s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1 → s.core.regs 4 = sc →
      (∀ u : ℕ, u < k → s.integerMemory (2 + (u : ℤ)) = 2 ^ u) →
      (∀ y, y < 0 → s.core.mem y = m0 y) →
      (∀ ℓ' : ℕ, ℓ' < ℓ → ∀ j : Fin (2 ^ k),
        s.core.mem ((ℓ' + (j : ℕ) * L : ℕ) : ℤ) = evW k σ z ℓ' j * sc) →
      ∃ t, t ≤ kk * (20 * 2 ^ k + k * (10 * 2 ^ k + 8) + 11) + 1 ∧
        (run Q s detTape t).core.pc = off + 79 ∧ (run Q s detTape t).halted = false ∧
        (∀ ℓ' : ℕ, ℓ' < L → ∀ j : Fin (2 ^ k),
          (run Q s detTape t).core.mem ((ℓ' + (j : ℕ) * L : ℕ) : ℤ) = evW k σ z ℓ' j * sc) ∧
        (run Q s detTape t).work = s.work + t := by
  intro kk
  induction kk with
  | zero =>
    intro ℓ s hlk hpc hh h16 h17 h3 h4 h0 h2 h13 h14 h15 h4r hst hneg hdone
    have hl : ℓ = L := by omega
    subst hl
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ := vl_exit Q off hE s hpc hh (by rw [h14, h16])
    exact ⟨1, by omega, g1, g2, fun ℓ' h j => by rw [g5]; exact hdone ℓ' h j, g7⟩
  | succ kk ih =>
    intro ℓ s hlk hpc hh h16 h17 h3 h4 h0 h2 h13 h14 h15 h4r hst hneg hdone
    have hl : ℓ < L := by omega
    have hL : 0 < L := by omega
    set d := 2 ^ k with hd
    have hdp : 0 < d := by positivity
    set fb : ℤ := ((L * d : ℕ) : ℤ) with hfb
    have hfb0 : 0 ≤ fb := by positivity
    -- head
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ :=
      vl_head Q off hE s hpc hh (by rw [h16, h14]; exact_mod_cast hl)
    set s1 := run Q s detTape 2 with hs1
    have f1 : ∀ x, x ≠ 18 → s1.core.ptrs x = s.core.ptrs x := g4
    -- signed input
    obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8⟩ :=
      vr_loop Q off hE d (ℓ * d) fb hfb0 (σ ℓ) z s1.core.mem d 0 s1 (by omega) g1 g2 g3
        (by rw [f1 3 (by decide), h3]) (by rw [f1 13 (by decide), h13])
        (by rw [f1 15 (by decide), h15]) (by rw [f1 17 (by decide), h17])
        (fun r hr => by rw [g6, hneg _ (by push_cast; omega)]; exact hsg ℓ hl r hr)
        (fun r hr => by rw [g6, hneg _ (by omega)]; exact hz r hr)
        (fun r' hr' => absurd hr' (Nat.not_lt_zero _)) (fun y _ => rfl)
    set s2 := run Q s1 detTape t2 with hs2
    have f2 : ∀ x, x ≠ 11 → x ≠ 18 → x ≠ 19 → s2.core.ptrs x = s.core.ptrs x :=
      fun x a b c => by rw [p3 x a b c, f1 x b]
    -- transform
    obtain ⟨T3, hT3, q1, q2, q3, q4, q5, q6, q7, q8, _⟩ :=
      fw_spec Q (off + 43) (emb_fw hE) k fb (fun r => σ ℓ r * z r) s2 (by rw [p1]) p2
        (by rw [f2 4 (by decide) (by decide) (by decide), h4])
        (by rw [f2 0 (by decide) (by decide) (by decide), h0])
        (by rw [f2 2 (by decide) (by decide) (by decide), h2])
        (by rw [f2 3 (by decide) (by decide) (by decide), h3])
        (by rw [f2 13 (by decide) (by decide) (by decide), h13])
        (fun u hu => by rw [p7, g7]; exact hst u hu) (fun x hx => p5 x hx)
    set s3 := run Q s2 detTape T3 with hs3
    have f3 : ∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 18 →
        x ≠ 19 → s3.core.ptrs x = s.core.ptrs x :=
      fun x a b c e f g h i j l => by rw [q3 x a b c e f g h i, f2 x h j l]
    -- output
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, _⟩ :=
      vj_init Q off hE s3 (by rw [q1]) q2
    set s4 := run Q s3 detTape 2 with hs4
    have f4 : ∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 18 →
        x ≠ 19 → x ≠ 20 → x ≠ 21 → s4.core.ptrs x = s.core.ptrs x :=
      fun x a b c e f g h i j l m n => by rw [r5 x m n, f3 x a b c e f g h i j l]
    have hreg4 : s4.core.regs 4 = sc := by
      rw [r6, q4 4 (by decide) (by decide) (by decide) (by decide), p4 4 (by decide) (by decide),
        g5, h4r]
    let w : ℕ → ℝ := fun j => if hj : j < d then evW k σ z ℓ ⟨j, hj⟩ else 0
    have hfar : ∀ j : ℕ, j < d → ((ℓ + j * L : ℕ) : ℤ) < fb := by
      intro j hj
      have : ℓ + j * L < L * d := cell_lt hl hj
      simp only [hfb]; exact_mod_cast this
    have h21 : s4.core.ptrs 21 = ((ℓ + 0 * L : ℕ) : ℤ) := by
      rw [r4, f3 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), h16]
      simp
    obtain ⟨t5, ht5, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10⟩ :=
      vj_loop Q off hE d L ℓ fb w sc s4.core.mem hL hfar d 0 s4 (by omega) r1 r2 r3 h21
        (by rw [f4 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h3])
        (by rw [f4 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h13])
        (by rw [f4 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h14]) hreg4
        (fun j' hj' => by
          rw [r7]
          have := q5 ⟨j', hj'⟩
          simp only [w, dif_pos hj']
          exact this)
        (fun j' hj' => absurd hj' (Nat.not_lt_zero _)) (fun y _ => rfl)
    set s5 := run Q s4 detTape t5 with hs5
    have f5 : ∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 16 →
        x ≠ 17 → x ≠ 18 → x ≠ 19 → x ≠ 20 → x ≠ 21 → s5.core.ptrs x = s.core.ptrs x :=
      fun x a b c e f g h i o p j l m n => by rw [u5 x h o p m n, f4 x a b c e f g h i j l m n]
    -- memory of s5 below fb is that of s, except the cells ℓ + j·L
    have mfr : ∀ y, y < fb → (∀ j' : ℕ, j' < d → y ≠ ((ℓ + j' * L : ℕ) : ℤ)) →
        s5.core.mem y = s.core.mem y := by
      intro y hy hne
      rw [u8 y hne, r7, q6 y (Or.inl hy), p6 y (Or.inl hy), g6]
    obtain ⟨T6, hT6, v1, v2, v3, v4⟩ :=
      ih (ℓ + 1) s5 (by omega) u1 u2
        (by rw [u3, f4 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h16]; push_cast; ring)
        (by rw [u4, f4 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h17, hd]; push_cast; ring)
        (by rw [f5 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h3])
        (by rw [f5 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h4])
        (by rw [f5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h0])
        (by rw [f5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h2])
        (by rw [f5 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h13])
        (by rw [f5 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h14])
        (by rw [f5 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h15])
        (by rw [u6 4 (by decide), hreg4])
        (fun u hu => by rw [u9, r8, q7, p7, g7]; exact hst u hu)
        (fun y hy => by
          rw [mfr y (by omega) (fun j' _ => by intro e; rw [e] at hy; omega)]
          exact hneg y hy)
        (by
          intro ℓ' hℓ' j
          rcases Nat.lt_or_ge ℓ' ℓ with h | h
          · have hc : ℓ' + (j : ℕ) * L < L * d := cell_lt (by omega) j.isLt
            have hc' : ((ℓ' + (j : ℕ) * L : ℕ) : ℤ) < fb := by simp only [hfb]; exact_mod_cast hc
            have hne : ∀ j' : ℕ, j' < d → ((ℓ' + (j : ℕ) * L : ℕ) : ℤ) ≠ ((ℓ + j' * L : ℕ) : ℤ) := by
              intro j' _ e
              have e' : ℓ' + (j : ℕ) * L = ℓ + j' * L := by exact_mod_cast e
              have := cell_inj (by omega : ℓ' < L) hl e'
              omega
            rw [mfr _ hc' hne]
            exact hdone ℓ' h j
          · have : ℓ' = ℓ := by omega
            subst this
            rw [u7 j j.isLt]
            have hj : (j : ℕ) < d := j.isLt
            simp only [w, dif_pos hj])
    refine ⟨2 + t2 + T3 + 2 + t5 + T6, ?_, ?_⟩
    · have e1 : (kk + 1) * (20 * 2 ^ k + k * (10 * 2 ^ k + 8) + 11) =
          kk * (20 * 2 ^ k + k * (10 * 2 ^ k + 8) + 11) + (20 * 2 ^ k + k * (10 * 2 ^ k + 8) + 11) := by
        ring
      rw [hd] at ht2 ht5
      omega
    have e5 : run Q s detTape (2 + t2 + T3 + 2 + t5) = s5 := by
      rw [run_add, run_add, run_add, run_add, ← hs1, ← hs2, ← hs3, ← hs4, ← hs5]
    rw [run_add, e5]
    refine ⟨v1, v2, v3, by rw [v4, u10, r9, q8, p8, g8]; ring⟩

/-- **The contract of `ev`.** From `pc = off`, with pointer `0` zero, `L` and `d = 2^k` in the
integer cells `0`, `1`, the signs `σ ℓ r` at `-d-1-(ℓd+r)` and the query `z r` at `-1-r`, the
program halts, and real cell `ℓ + j·L` holds `(√(L·d))⁻¹ · (H_k (σ ℓ ⊙ z))_j`. -/
theorem ev_spec (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (k L : ℕ)
    (σ : ℕ → ℕ → ℝ) (z : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 0) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (hL : s.integerMemory 0 = L) (hd : s.integerMemory 1 = ((2 ^ k : ℕ) : ℤ))
    (hsg : ∀ ℓ : ℕ, ℓ < L → ∀ r : ℕ, r < 2 ^ k →
      s.core.mem (-((2 ^ k : ℕ) : ℤ) - 1 - ((ℓ * 2 ^ k : ℕ) : ℤ) - r) = σ ℓ r)
    (hz : ∀ r : ℕ, r < 2 ^ k → s.core.mem (-(r : ℤ) - 1) = z r) :
    ∃ t, t ≤ 23 + 6 * k + 4 * L + L * (20 * 2 ^ k + k * (10 * 2 ^ k + 8) + 11) ∧
      (run Q s detTape t).halted = true ∧
      (∀ ℓ : ℕ, ℓ < L → ∀ j : Fin (2 ^ k),
        (run Q s detTape t).core.mem ((ℓ + (j : ℕ) * L : ℕ) : ℤ) =
          evW k σ z ℓ j * (1 / Real.sqrt ((L : ℝ) * (2 ^ k : ℕ)))) ∧
      (run Q s detTape t).work = s.work + t := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, _⟩ :=
    ev_init Q off hE L ((2 ^ k : ℕ) : ℤ) s hpc hh (by rw [h0]; exact hL) hd
  set s1 := run Q s detTape 7 with hs1
  obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
    st_loop Q off hE k k 0 s1 (by omega) g1 g2 g5 (by rw [g8]; simp) (by rw [g6]; simp)
      (by rw [g7]; simp) (fun v hv => absurd hv (Nat.not_lt_zero _))
  set s2 := run Q s1 detTape t2 with hs2
  have f2 : ∀ x, x ≠ 1 → x ≠ 2 → x ≠ 3 → x ≠ 4 → x ≠ 6 → x ≠ 7 → x ≠ 10 → x ≠ 13 → x ≠ 14 →
      x ≠ 15 → s2.core.ptrs x = s.core.ptrs x :=
    fun x a b c e f g h i j l => by rw [p7 x e f g h i l, g10 x a b c e f g j]
  obtain ⟨t3, ht3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
    ab_loop Q off hE L (2 ^ k) L 0 s2 (by omega) p1 p2 p4
      (by rw [p7 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9])
      (by rw [p7 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g5])
      (by rw [p5]; simp)
  set s3 := run Q s2 detTape t3 with hs3
  have p3' : s2.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ) := by
    rw [p7 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g5]
  have hp3 : ∀ x, x ≠ 10 → x ≠ 13 → x ≠ 16 → x ≠ 17 → s3.core.ptrs x = s2.core.ptrs x := q6
  have hsc : s3.core.regs 4 = 1 / Real.sqrt ((L : ℝ) * (2 ^ k : ℕ)) := by
    rw [q7, p8, g9, g5]
    push_cast; rfl
  have hmem3 : s3.core.mem = s.core.mem := by rw [q8, p10, g12]
  obtain ⟨t4, ht4, v1, v2, v3, v4⟩ :=
    vl_loop Q off hE k L σ z (1 / Real.sqrt ((L : ℝ) * (2 ^ k : ℕ))) s.core.mem hsg hz L 0 s3
      (by omega) q1 q2 (by rw [q4]; simp) (by rw [q5]; simp)
      (by rw [hp3 3 (by decide) (by decide) (by decide) (by decide), p3'])
      (by rw [hp3 4 (by decide) (by decide) (by decide) (by decide), p3])
      (by rw [hp3 0 (by decide) (by decide) (by decide) (by decide),
        p7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        g10 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h0])
      (by rw [hp3 2 (by decide) (by decide) (by decide) (by decide),
        p7 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g4])
      q3
      (by rw [hp3 14 (by decide) (by decide) (by decide) (by decide),
        p7 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9])
      (by rw [hp3 15 (by decide) (by decide) (by decide) (by decide), p6, g5])
      hsc (fun u hu => by rw [q9]; exact p11 u hu) (fun y _ => by rw [hmem3])
      (fun ℓ' h => absurd h (Nat.not_lt_zero _))
  set s4 := run Q s3 detTape t4 with hs4
  obtain ⟨w1, w2, w3⟩ := ev_halt Q off hE s4 v1 v2
  refine ⟨7 + t2 + t3 + t4 + 1, by omega, ?_⟩
  have e4 : run Q s detTape (7 + t2 + t3 + t4) = s4 := by
    rw [run_add, run_add, run_add, ← hs1, ← hs2, ← hs3, ← hs4]
  rw [run_add, e4]
  exact ⟨w1, fun ℓ h j => by rw [w2]; exact v3 ℓ h j, by rw [w3, v4, q10, p13, g14]; ring⟩

end DetANN.Supplement.Thm32

-- ===== T32_EvFinal =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM.QP

/-- The signs of `ξ` as reals indexed by `ℕ`. -/
noncomputable def sgnArr {L d : ℕ} (ξ : Fin L → Fin d → Bool) (ℓ r : ℕ) : ℝ :=
  if h : ℓ < L ∧ r < d then signOf (ξ ⟨ℓ, h.1⟩ ⟨r, h.2⟩) else 0

/-- A vector of `ℝ^d` as reals indexed by `ℕ`. -/
noncomputable def vecArr {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) (r : ℕ) : ℝ :=
  if h : r < d then z ⟨r, h⟩ else 0

lemma evW_signed (k L : ℕ) (ξ : Fin L → Fin (2 ^ k) → Bool) (z : EuclideanSpace ℝ (Fin (2 ^ k)))
    (ℓ : Fin L) (j : Fin (2 ^ k)) :
    evW k (sgnArr ξ) (vecArr z) ℓ j * (1 / Real.sqrt ((L : ℝ) * (2 ^ k : ℕ))) =
      signedBlocks (sylvester k) L ξ j z ℓ := by
  simp only [evW, signedBlocks, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
    sgnArr, vecArr, ℓ.isLt, Fin.is_lt, and_self, dif_pos, Fin.eta]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Matrix.of_apply, one_div]
  push_cast
  ring

lemma ev_work (k L : ℕ) (hL : 1 ≤ L) :
    23 + 6 * k + 4 * L + L * (20 * 2 ^ k + k * (10 * 2 ^ k + 8) + 11) ≤ 82 * (L * 2 ^ k * (1 + k)) := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have a : 1 ≤ L * 2 ^ k := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith [Nat.mul_le_mul a (Nat.le_refl k), Nat.mul_le_mul_left L h1]

/-- **`ev` evaluates the signed Hadamard blocks.** -/
theorem ev_signed (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (k L : ℕ) (hL : 1 ≤ L)
    (ξ : Fin L → Fin (2 ^ k) → Bool) (z : EuclideanSpace ℝ (Fin (2 ^ k))) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) (h0 : s.core.ptrs 0 = 0)
    (hLm : s.integerMemory 0 = L) (hd : s.integerMemory 1 = 2 ^ k)
    (hsg : ∀ (ℓ : Fin L) (r : Fin (2 ^ k)),
      s.core.mem (-(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r)) = signOf (ξ ℓ r))
    (hz : ∀ r : Fin (2 ^ k), s.core.mem (-1 - (r : ℤ)) = z r) :
    ∃ t, t ≤ 82 * (L * 2 ^ k * (1 + k)) ∧ (run Q s detTape t).halted = true ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ (j : Fin (2 ^ k)) (ℓ : Fin L),
        (run Q s detTape t).core.mem ((j : ℤ) * L + ℓ) = signedBlocks (sylvester k) L ξ j z ℓ := by
  obtain ⟨t, ht, h1, h2, h3⟩ := ev_spec Q off hE k L (sgnArr ξ) (vecArr z) s (by rw [hpc]; rfl) hh h0
    hLm (by rw [hd]; push_cast; rfl)
    (fun ℓ hℓ r hr => by
      have := hsg ⟨ℓ, hℓ⟩ ⟨r, hr⟩
      simp only [sgnArr, hℓ, hr, and_self, dif_pos]
      rw [← this]; congr 1; push_cast; ring)
    (fun r hr => by
      have := hz ⟨r, hr⟩
      simp only [vecArr, hr, dif_pos]
      rw [← this]; congr 1; ring)
  refine ⟨t, le_trans ht (ev_work k L hL), h1, h3, fun j ℓ => ?_⟩
  have := h2 ℓ ℓ.isLt j
  rw [show ((j : ℤ) * L + ℓ) = ((ℓ + (j : ℕ) * L : ℕ) : ℤ) by push_cast; ring, this]
  exact evW_signed k L ξ z ℓ j

end DetANN.Supplement.Thm32

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

theorem _root_.solution :
    ∀ (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (k L : ℕ) (hL : 1 ≤ L)
    (ξ : Fin L → Fin (2 ^ k) → Bool) (z : EuclideanSpace ℝ (Fin (2 ^ k))) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) (h0 : s.core.ptrs 0 = 0)
    (hLm : s.integerMemory 0 = L) (hd : s.integerMemory 1 = 2 ^ k)
    (hsg : ∀ (ℓ : Fin L) (r : Fin (2 ^ k)),
      s.core.mem (-(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r)) = signOf (ξ ℓ r))
    (hz : ∀ r : Fin (2 ^ k), s.core.mem (-1 - (r : ℤ)) = z r),
    ∃ t, t ≤ 82 * (L * 2 ^ k * (1 + k)) ∧ (run Q s detTape t).halted = true ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ (j : Fin (2 ^ k)) (ℓ : Fin L),
        (run Q s detTape t).core.mem ((j : ℤ) * L + ℓ) = signedBlocks (sylvester k) L ξ j z ℓ :=
  DetANN.Supplement.Thm32.ev_signed

end DetANN.Supplement.Thm32

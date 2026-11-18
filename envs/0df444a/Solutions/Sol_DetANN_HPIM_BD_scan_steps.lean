-- Prove2me | solution 1 for DetANN.HPIM.BD.scan_steps
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T21:34:27.785065+00:00
-- url     : https://prove2.me/submissions/188064b9-6c29-49e6-8042-d8dbc895f0d9

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_DetANN_HPIMBuildProg

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

-- ===== BD_Prog =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep

lemma len_init (off : ℕ) : (bd_init off).length = 34 := rfl

lemma len_disp (off : ℕ) : (bd_disp off).length = 19 := rfl

lemma len_dl (off : ℕ) : (bd_dl off).length = 33 := rfl

lemma len_near (off : ℕ) : (bd_near off).length = 30 := rfl

lemma len_fi (off : ℕ) : (bd_fi off).length = 18 := rfl

lemma len_tb (off : ℕ) : (bd_tb off).length = 27 := rfl

lemma len_sg0 (off : ℕ) : (bd_sg0 off).length = 11 := rfl

lemma len_sg (off : ℕ) : (bd_sg off).length = 25 := rfl

lemma len_split (off : ℕ) : (bd_split off).length = 29 := rfl

lemma len_split2 (off : ℕ) : (bd_split2 off).length = 32 := rfl

lemma len_cs (off : ℕ) : (bd_cs off).length = 22 := rfl

lemma len_cv (off : ℕ) : (bd_cv off).length = 24 := rfl

lemma len_cv2 (off : ℕ) : (bd_cv2 off).length = 22 := rfl

lemma len_cv3 (off : ℕ) : (bd_cv3 off).length = 22 := rfl

lemma len_cv4 (off : ℕ) : (bd_cv4 off).length = 24 := rfl

lemma len_ce (off : ℕ) : (bd_ce off).length = 11 := rfl

lemma emb_init {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_init off) (off + 0) := by
  have h := embeds_app_left (hE)
  simpa only [Nat.add_zero] using h

lemma emb_disp {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_disp off) (off + 34) := by
  have h := embeds_app_left (embeds_app_right (hE))
  simpa only [len_init, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_dl {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_dl off) (off + 53) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (hE)))
  simpa only [len_init, len_disp, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_near {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_near off) (off + 86) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (hE))))
  simpa only [len_init, len_disp, len_dl, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_fi {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_fi off) (off + 116) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE)))))
  simpa only [len_init, len_disp, len_dl, len_near, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_leaf {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_leaf off) (off + 383) := by
  have h := embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE))))))))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, len_cs, len_cv, len_cv2, len_cv3, len_cv4, len_ce, Nat.add_assoc, Nat.reduceAdd] using h

end DetANN.HPIM.BD

-- ===== BD_PrfA =====
namespace DetANN.HPIM.BD.SA

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

variable {m n : ℕ}

/-- Constants, the root box allocation. -/
lemma seg_init (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 0) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 13).core.pc = off + 13 ∧
      (run Q s detTape 13).halted = false ∧
      (run Q s detTape 13).core.ptrs 14 = s.core.ptrs 14 - 2 * s.core.ptrs 1 ∧
      (run Q s detTape 13).core.ptrs 40 = s.core.ptrs 13 ∧
      (run Q s detTape 13).core.ptrs 43 = s.core.ptrs 14 - 2 * s.core.ptrs 1 ∧
      (run Q s detTape 13).core.ptrs 46 = 0 ∧
      (run Q s detTape 13).core.ptrs 60 = 2 * s.core.ptrs 1 ∧
      (run Q s detTape 13).core.ptrs 68 = 1 ∧
      (run Q s detTape 13).core.ptrs 69 = 0 ∧
      (∀ x, x ≠ 14 → x ≠ 40 → x ≠ 43 → x ≠ 46 → x ≠ 60 → x ≠ 68 → x ≠ 69 → (run Q s detTape 13).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 13).core.regs 40 = (s.core.regs 11 * s.core.regs 11) ∧
      (run Q s detTape 13).core.regs 41 = ((s.core.regs 12 * s.core.regs 11) * (s.core.regs 12 * s.core.regs 11)) ∧
      (run Q s detTape 13).core.regs 47 = (s.core.regs 12 * s.core.regs 11) ∧
      (run Q s detTape 13).core.regs 49 = (s.core.regs 11 + s.core.regs 11) ∧
      (run Q s detTape 13).core.regs 50 = (0 : ℝ) ∧
      (run Q s detTape 13).core.regs 53 = (2 : ℝ) ∧
      (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 53 → (run Q s detTape 13).core.regs x = s.core.regs x) ∧
      (run Q s detTape 13).core.mem = s.core.mem ∧
      (run Q s detTape 13).integerMemory = s.integerMemory ∧
      (run Q s detTape 13).work = s.work + 13 ∧
      cellsWritten Q s 13 = ∅ := by
  have hS := emb_init hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- One step of the root box copy. -/
lemma icp_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State)
    (hpc : s.core.pc = off + 13) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 17 + s.core.ptrs 46) = x)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 60)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 13 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 7).core.ptrs 50 = s.core.ptrs 43 + s.core.ptrs 46 ∧
      (∀ x, x ≠ 46 → x ≠ 50 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 55 = x ∧
      (∀ x, x ≠ 55 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem (s.core.ptrs 43 + s.core.ptrs 46) = x ∧
      (∀ z, z ≠ s.core.ptrs 43 + s.core.ptrs 46 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 43 + s.core.ptrs 46) := by
  have hS := emb_init hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 17 + ptrs 46 → mem z = x := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma icp_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 13) (hh : s.halted = false)
    (hb0 : s.core.ptrs 60 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 20 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_init hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Root slot and the first task. -/
lemma seg_icd (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 20) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 14).core.pc = off + 34 ∧
      (run Q s detTape 14).halted = false ∧
      (run Q s detTape 14).core.ptrs 13 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 14).core.ptrs 42 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 14).core.ptrs 44 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 14).core.ptrs 57 = s.core.ptrs 13 - 2 ∧
      (run Q s detTape 14).core.ptrs 59 = s.core.ptrs 13 - 1 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 44 → x ≠ 57 → x ≠ 59 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 14).core.regs = s.core.regs ∧
      (run Q s detTape 14).core.mem = s.core.mem ∧
      (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 43 ∧
      (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 40 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 14).work = s.work + 14 ∧
      ∀ c ∈ cellsWritten Q s 14, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) := by
  have hS := emb_init hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

lemma disp_end (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false)
    (hb0 : s.core.ptrs 40 ≤ s.core.ptrs 42)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 395 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_disp hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

lemma seg_end (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (rt : ℤ) (s : State)
    (hpc : s.core.pc = off + 395) (hh : s.halted = false)
    (fi0 : s.integerMemory (s.core.ptrs 59) = rt)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 396 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 17 = rt ∧
      (∀ x, x ≠ 17 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_leaf hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fi0 hm1 ⊢
  subst hh
  have ei0 : ∀ z, z = ptrs 59 → im z = rt := fun z hz => hz ▸ fi0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0]
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

/-- Pop a task and allocate the near box. -/
lemma seg_pop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (ep esl elink : ℤ) (s : State)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false)
    (fi0 : s.integerMemory (s.core.ptrs 42) = ep)
    (fi1 : s.integerMemory (s.core.ptrs 42 + 1) = esl)
    (fi2 : s.integerMemory (s.core.ptrs 42 + 2) = elink)
    (hb0 : s.core.ptrs 42 < s.core.ptrs 40)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 11).core.pc = off + 45 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 14 = s.core.ptrs 14 - s.core.ptrs 60 ∧
      (run Q s detTape 11).core.ptrs 42 = elink ∧
      (run Q s detTape 11).core.ptrs 43 = ep ∧
      (run Q s detTape 11).core.ptrs 44 = esl ∧
      (run Q s detTape 11).core.ptrs 45 = 0 ∧
      (run Q s detTape 11).core.ptrs 48 = s.core.ptrs 14 - s.core.ptrs 60 ∧
      (run Q s detTape 11).core.ptrs 49 = 0 ∧
      (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 42 + 2 ∧
      (∀ x, x ≠ 14 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 48 → x ≠ 49 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs = s.core.regs ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      cellsWritten Q s 11 = ∅ := by
  have hS := emb_disp hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fi0 fi1 fi2 hb0 hm1 ⊢
  subst hh
  have ei0 : ∀ z, z = ptrs 42 → im z = ep := fun z hz => hz ▸ fi0
  have ei1 : ∀ z, z = ptrs 42 + 1 → im z = esl := fun z hz => hz ▸ fi1
  have ei2 : ∀ z, z = ptrs 42 + 2 → im z = elink := fun z hz => hz ▸ fi2
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0, ei1, ei2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0, ei1, ei2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0, ei1, ei2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma scan_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 45) (hh : s.halted = false)
    (hb0 : s.core.ptrs 11 ≤ s.core.ptrs 45)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 131 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_disp hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- Address of point `i`; zero both sums. -/
lemma scan_head (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (ki pa : ℤ) (s : State)
    (hpc : s.core.pc = off + 45) (hh : s.halted = false)
    (fi0 : s.integerMemory (s.core.ptrs 10 + s.core.ptrs 45) = ki)
    (fi1 : s.integerMemory (s.core.ptrs 12 + ki) = pa)
    (hb0 : s.core.ptrs 45 < s.core.ptrs 11)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 8).core.pc = off + 53 ∧
      (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 46 = 0 ∧
      (run Q s detTape 8).core.ptrs 47 = pa ∧
      (run Q s detTape 8).core.ptrs 57 = s.core.ptrs 12 + ki ∧
      (∀ x, x ≠ 46 → x ≠ 47 → x ≠ 57 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs 42 = (0 : ℝ) ∧
      (run Q s detTape 8).core.regs 43 = (0 : ℝ) ∧
      (∀ x, x ≠ 42 → x ≠ 43 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧
      (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧
      cellsWritten Q s 8 = ∅ := by
  have hS := emb_disp hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fi0 fi1 hb0 hm1 ⊢
  subst hh
  have ei0 : ∀ z, z = ptrs 10 + ptrs 45 → im z = ki := fun z hz => hz ▸ fi0
  have ei1 : ∀ z, z = ptrs 12 + ki → im z = pa := fun z hz => hz ▸ fi1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0, ei1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [ei0, ei1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma dl_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 53) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 86 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_dl hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- One coordinate of both squared distances. -/
lemma dl_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x lo hi : ℝ) (s : State)
    (hpc : s.core.pc = off + 53) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x)
    (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo)
    (fr2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 33).core.pc = off + 53 ∧
      (run Q s detTape 33).halted = false ∧
      (run Q s detTape 33).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 33).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 33).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 33).core.regs 42 = (s.core.regs 42 + (((((lo - x) + (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) + Real.sqrt (((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) * ((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)))) / s.core.regs 53) * ((((lo - x) + (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) + Real.sqrt (((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) * ((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)))) / s.core.regs 53))) ∧
      (run Q s detTape 33).core.regs 43 = (s.core.regs 43 + (((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) * ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53))) ∧
      (run Q s detTape 33).core.regs 44 = x ∧
      (run Q s detTape 33).core.regs 45 = lo ∧
      (run Q s detTape 33).core.regs 46 = hi ∧
      (run Q s detTape 33).core.regs 47 = ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) ∧
      (run Q s detTape 33).core.regs 48 = (hi - x) ∧
      (run Q s detTape 33).core.regs 54 = (((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) * ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53)) ∧
      (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 54 → (run Q s detTape 33).core.regs x = s.core.regs x) ∧
      (run Q s detTape 33).core.mem = s.core.mem ∧
      (run Q s detTape 33).integerMemory = s.integerMemory ∧
      (run Q s detTape 33).work = s.work + 33 ∧
      cellsWritten Q s 33 = ∅ := by
  have hS := emb_dl hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 fr2 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 47 + ptrs 46 → mem z = x := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 43 + ptrs 46 → mem z = lo := fun z hz => hz ▸ fr1
  have er2 : ∀ z, z = ptrs 43 + ptrs 46 + ptrs 1 → mem z = hi := fun z hz => hz ▸ fr2
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma dd_far (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 86) (hh : s.halted = false)
    (hb0 : ¬ (s.core.regs 42 - s.core.regs 40) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 126 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 3).core.regs 54 = (s.core.regs 42 - s.core.regs 40) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_near hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma dd_good (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 86) (hh : s.halted = false)
    (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0)
    (hb1 : (s.core.regs 43 - s.core.regs 41) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 4).core.pc = off + 128 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 4).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_near hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma dd_up (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 86) (hh : s.halted = false)
    (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0)
    (hb1 : ¬ (s.core.regs 43 - s.core.regs 41) ≤ 0)
    (hb2 : s.core.ptrs 69 < s.core.ptrs 49)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 6).core.pc = off + 93 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 46 = 0 ∧
      (∀ x, x ≠ 46 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_near hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 hb2 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma dd_fi (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 86) (hh : s.halted = false)
    (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0)
    (hb1 : ¬ (s.core.regs 43 - s.core.regs 41) ≤ 0)
    (hb2 : s.core.ptrs 49 ≤ s.core.ptrs 69)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 6).core.pc = off + 116 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 46 = 0 ∧
      (∀ x, x ≠ 46 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_near hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 hb2 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma up_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 93) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 126 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_near hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- One coordinate of the running min and max. -/
lemma up_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x mn mx : ℝ) (s : State)
    (hpc : s.core.pc = off + 93) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x)
    (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn)
    (fr2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 23).core.pc = off + 93 ∧
      (run Q s detTape 23).halted = false ∧
      (run Q s detTape 23).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 23).core.regs 44 = x ∧
      (run Q s detTape 23).core.regs 45 = mx ∧
      (run Q s detTape 23).core.regs 47 = (((mx + x) + Real.sqrt ((mx - x) * (mx - x))) / s.core.regs 53) ∧
      (run Q s detTape 23).core.regs 54 = Real.sqrt ((mx - x) * (mx - x)) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 23).core.regs x = s.core.regs x) ∧
      (run Q s detTape 23).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = (((mn + x) - Real.sqrt ((mn - x) * (mn - x))) / s.core.regs 53) ∧
      (run Q s detTape 23).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = (((mx + x) + Real.sqrt ((mx - x) * (mx - x))) / s.core.regs 53) ∧
      (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 23).core.mem z = s.core.mem z) ∧
      (run Q s detTape 23).integerMemory = s.integerMemory ∧
      (run Q s detTape 23).work = s.work + 23 ∧
      ∀ c ∈ cellsWritten Q s 23, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) := by
  have hS := emb_near hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 fr2 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 47 + ptrs 46 → mem z = x := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 48 + ptrs 46 → mem z = mn := fun z hz => hz ▸ fr1
  have er2 : ∀ z, z = ptrs 48 + ptrs 46 + ptrs 1 → mem z = mx := fun z hz => hz ▸ fr2
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h <;> subst h <;> simp <;> omega)⟩

lemma fi_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State)
    (hpc : s.core.pc = off + 116) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 9).core.pc = off + 116 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 9).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs 44 = x ∧
      (∀ x, x ≠ 44 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧
      (run Q s detTape 9).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = x ∧
      (run Q s detTape 9).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = x ∧
      (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) := by
  have hS := emb_fi hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 47 + ptrs 46 → mem z = x := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h <;> subst h <;> simp <;> omega)⟩

lemma fi_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 116) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 2).core.pc = off + 126 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 49 = 1 ∧
      (∀ x, x ≠ 49 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_fi hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma seg_next (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 126) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 2).core.pc = off + 45 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 45 = s.core.ptrs 45 + 1 ∧
      (∀ x, x ≠ 45 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_fi hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma seg_good (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 128) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 383 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 61 = s.core.ptrs 45 + 1 ∧
      (∀ x, x ≠ 61 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_fi hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma scd_out (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 131) (hh : s.halted = false)
    (hb0 : s.core.ptrs 49 ≤ s.core.ptrs 69)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 2).core.pc = off + 383 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 61 = 0 ∧
      (∀ x, x ≠ 61 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_fi hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma scd_tb (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 131) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 49)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 134 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 46 = 0 ∧
      (run Q s detTape 3).core.ptrs 61 = 0 ∧
      (∀ x, x ≠ 46 → x ≠ 61 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_fi hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

theorem scan_steps' :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 0) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 13).core.pc = off + 13 ∧ (run Q s detTape 13).halted = false ∧ (run Q s detTape 13).core.ptrs 14 = s.core.ptrs 14 - 2 * s.core.ptrs 1 ∧ (run Q s detTape 13).core.ptrs 40 = s.core.ptrs 13 ∧ (run Q s detTape 13).core.ptrs 43 = s.core.ptrs 14 - 2 * s.core.ptrs 1 ∧ (run Q s detTape 13).core.ptrs 46 = 0 ∧ (run Q s detTape 13).core.ptrs 60 = 2 * s.core.ptrs 1 ∧ (run Q s detTape 13).core.ptrs 68 = 1 ∧ (run Q s detTape 13).core.ptrs 69 = 0 ∧ (∀ x, x ≠ 14 → x ≠ 40 → x ≠ 43 → x ≠ 46 → x ≠ 60 → x ≠ 68 → x ≠ 69 → (run Q s detTape 13).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 13).core.regs 40 = (s.core.regs 11 * s.core.regs 11) ∧ (run Q s detTape 13).core.regs 41 = ((s.core.regs 12 * s.core.regs 11) * (s.core.regs 12 * s.core.regs 11)) ∧ (run Q s detTape 13).core.regs 47 = (s.core.regs 12 * s.core.regs 11) ∧ (run Q s detTape 13).core.regs 49 = (s.core.regs 11 + s.core.regs 11) ∧ (run Q s detTape 13).core.regs 50 = (0 : ℝ) ∧ (run Q s detTape 13).core.regs 53 = (2 : ℝ) ∧ (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 53 → (run Q s detTape 13).core.regs x = s.core.regs x) ∧ (run Q s detTape 13).core.mem = s.core.mem ∧ (run Q s detTape 13).integerMemory = s.integerMemory ∧ (run Q s detTape 13).work = s.work + 13 ∧ cellsWritten Q s 13 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State) (hpc : s.core.pc = off + 13) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 17 + s.core.ptrs 46) = x) (hb0 : s.core.ptrs 46 < s.core.ptrs 60) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 13 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 7).core.ptrs 50 = s.core.ptrs 43 + s.core.ptrs 46 ∧ (∀ x, x ≠ 46 → x ≠ 50 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs 55 = x ∧ (∀ x, x ≠ 55 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem (s.core.ptrs 43 + s.core.ptrs 46) = x ∧ (∀ z, z ≠ s.core.ptrs 43 + s.core.ptrs 46 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 43 + s.core.ptrs 46)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 13) (hh : s.halted = false) (hb0 : s.core.ptrs 60 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 20 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 20) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 14).core.pc = off + 34 ∧ (run Q s detTape 14).halted = false ∧ (run Q s detTape 14).core.ptrs 13 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 14).core.ptrs 42 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 14).core.ptrs 44 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 14).core.ptrs 57 = s.core.ptrs 13 - 2 ∧ (run Q s detTape 14).core.ptrs 59 = s.core.ptrs 13 - 1 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 44 → x ≠ 57 → x ≠ 59 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 43 ∧ (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 13 - 1 ∧ (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 40 ∧ (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 14).work = s.work + 14 ∧ ∀ c ∈ cellsWritten Q s 14, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hb0 : s.core.ptrs 40 ≤ s.core.ptrs 42) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 395 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (rt : ℤ) (s : State) (hpc : s.core.pc = off + 395) (hh : s.halted = false) (fi0 : s.integerMemory (s.core.ptrs 59) = rt) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 396 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs 17 = rt ∧ (∀ x, x ≠ 17 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (ep esl elink : ℤ) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (fi0 : s.integerMemory (s.core.ptrs 42) = ep) (fi1 : s.integerMemory (s.core.ptrs 42 + 1) = esl) (fi2 : s.integerMemory (s.core.ptrs 42 + 2) = elink) (hb0 : s.core.ptrs 42 < s.core.ptrs 40) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 11).core.pc = off + 45 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 14 = s.core.ptrs 14 - s.core.ptrs 60 ∧ (run Q s detTape 11).core.ptrs 42 = elink ∧ (run Q s detTape 11).core.ptrs 43 = ep ∧ (run Q s detTape 11).core.ptrs 44 = esl ∧ (run Q s detTape 11).core.ptrs 45 = 0 ∧ (run Q s detTape 11).core.ptrs 48 = s.core.ptrs 14 - s.core.ptrs 60 ∧ (run Q s detTape 11).core.ptrs 49 = 0 ∧ (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 42 + 2 ∧ (∀ x, x ≠ 14 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 48 → x ≠ 49 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).integerMemory = s.integerMemory ∧ (run Q s detTape 11).work = s.work + 11 ∧ cellsWritten Q s 11 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 45) (hh : s.halted = false) (hb0 : s.core.ptrs 11 ≤ s.core.ptrs 45) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 131 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (ki pa : ℤ) (s : State) (hpc : s.core.pc = off + 45) (hh : s.halted = false) (fi0 : s.integerMemory (s.core.ptrs 10 + s.core.ptrs 45) = ki) (fi1 : s.integerMemory (s.core.ptrs 12 + ki) = pa) (hb0 : s.core.ptrs 45 < s.core.ptrs 11) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 8).core.pc = off + 53 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 46 = 0 ∧ (run Q s detTape 8).core.ptrs 47 = pa ∧ (run Q s detTape 8).core.ptrs 57 = s.core.ptrs 12 + ki ∧ (∀ x, x ≠ 46 → x ≠ 47 → x ≠ 57 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs 42 = (0 : ℝ) ∧ (run Q s detTape 8).core.regs 43 = (0 : ℝ) ∧ (∀ x, x ≠ 42 → x ≠ 43 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).integerMemory = s.integerMemory ∧ (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 53) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 86 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x lo hi : ℝ) (s : State) (hpc : s.core.pc = off + 53) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x) (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo) (fr2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 33).core.pc = off + 53 ∧ (run Q s detTape 33).halted = false ∧ (run Q s detTape 33).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 33).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 33).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 33).core.regs 42 = (s.core.regs 42 + (((((lo - x) + (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) + Real.sqrt (((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) * ((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)))) / s.core.regs 53) * ((((lo - x) + (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) + Real.sqrt (((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) * ((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)))) / s.core.regs 53))) ∧ (run Q s detTape 33).core.regs 43 = (s.core.regs 43 + (((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) * ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53))) ∧ (run Q s detTape 33).core.regs 44 = x ∧ (run Q s detTape 33).core.regs 45 = lo ∧ (run Q s detTape 33).core.regs 46 = hi ∧ (run Q s detTape 33).core.regs 47 = ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) ∧ (run Q s detTape 33).core.regs 48 = (hi - x) ∧ (run Q s detTape 33).core.regs 54 = (((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) * ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53)) ∧ (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 54 → (run Q s detTape 33).core.regs x = s.core.regs x) ∧ (run Q s detTape 33).core.mem = s.core.mem ∧ (run Q s detTape 33).integerMemory = s.integerMemory ∧ (run Q s detTape 33).work = s.work + 33 ∧ cellsWritten Q s 33 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 86) (hh : s.halted = false) (hb0 : ¬ (s.core.regs 42 - s.core.regs 40) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 126 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs = s.core.ptrs ∧ (run Q s detTape 3).core.regs 54 = (s.core.regs 42 - s.core.regs 40) ∧ (∀ x, x ≠ 54 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 86) (hh : s.halted = false) (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0) (hb1 : (s.core.regs 43 - s.core.regs 41) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 4).core.pc = off + 128 ∧ (run Q s detTape 4).halted = false ∧ (run Q s detTape 4).core.ptrs = s.core.ptrs ∧ (run Q s detTape 4).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧ (∀ x, x ≠ 54 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧ (run Q s detTape 4).core.mem = s.core.mem ∧ (run Q s detTape 4).integerMemory = s.integerMemory ∧ (run Q s detTape 4).work = s.work + 4 ∧ cellsWritten Q s 4 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 86) (hh : s.halted = false) (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0) (hb1 : ¬ (s.core.regs 43 - s.core.regs 41) ≤ 0) (hb2 : s.core.ptrs 69 < s.core.ptrs 49) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 6).core.pc = off + 93 ∧ (run Q s detTape 6).halted = false ∧ (run Q s detTape 6).core.ptrs 46 = 0 ∧ (∀ x, x ≠ 46 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 6).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧ (∀ x, x ≠ 54 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧ (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).integerMemory = s.integerMemory ∧ (run Q s detTape 6).work = s.work + 6 ∧ cellsWritten Q s 6 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 86) (hh : s.halted = false) (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0) (hb1 : ¬ (s.core.regs 43 - s.core.regs 41) ≤ 0) (hb2 : s.core.ptrs 49 ≤ s.core.ptrs 69) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 6).core.pc = off + 116 ∧ (run Q s detTape 6).halted = false ∧ (run Q s detTape 6).core.ptrs 46 = 0 ∧ (∀ x, x ≠ 46 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 6).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧ (∀ x, x ≠ 54 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧ (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).integerMemory = s.integerMemory ∧ (run Q s detTape 6).work = s.work + 6 ∧ cellsWritten Q s 6 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 93) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 126 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x mn mx : ℝ) (s : State) (hpc : s.core.pc = off + 93) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x) (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn) (fr2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 23).core.pc = off + 93 ∧ (run Q s detTape 23).halted = false ∧ (run Q s detTape 23).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 23).core.regs 44 = x ∧ (run Q s detTape 23).core.regs 45 = mx ∧ (run Q s detTape 23).core.regs 47 = (((mx + x) + Real.sqrt ((mx - x) * (mx - x))) / s.core.regs 53) ∧ (run Q s detTape 23).core.regs 54 = Real.sqrt ((mx - x) * (mx - x)) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 23).core.regs x = s.core.regs x) ∧ (run Q s detTape 23).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = (((mn + x) - Real.sqrt ((mn - x) * (mn - x))) / s.core.regs 53) ∧ (run Q s detTape 23).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = (((mx + x) + Real.sqrt ((mx - x) * (mx - x))) / s.core.regs 53) ∧ (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 23).core.mem z = s.core.mem z) ∧ (run Q s detTape 23).integerMemory = s.integerMemory ∧ (run Q s detTape 23).work = s.work + 23 ∧ ∀ c ∈ cellsWritten Q s 23, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State) (hpc : s.core.pc = off + 116) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 9).core.pc = off + 116 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 9).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs 44 = x ∧ (∀ x, x ≠ 44 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧ (run Q s detTape 9).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = x ∧ (run Q s detTape 9).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = x ∧ (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 116) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 2).core.pc = off + 126 ∧ (run Q s detTape 2).halted = false ∧ (run Q s detTape 2).core.ptrs 49 = 1 ∧ (∀ x, x ≠ 49 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 126) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 2).core.pc = off + 45 ∧ (run Q s detTape 2).halted = false ∧ (run Q s detTape 2).core.ptrs 45 = s.core.ptrs 45 + 1 ∧ (∀ x, x ≠ 45 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 128) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 383 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 61 = s.core.ptrs 45 + 1 ∧ (∀ x, x ≠ 61 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 131) (hh : s.halted = false) (hb0 : s.core.ptrs 49 ≤ s.core.ptrs 69) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 2).core.pc = off + 383 ∧ (run Q s detTape 2).halted = false ∧ (run Q s detTape 2).core.ptrs 61 = 0 ∧ (∀ x, x ≠ 61 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 131) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 49) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 134 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 46 = 0 ∧ (run Q s detTape 3).core.ptrs 61 = 0 ∧ (∀ x, x ≠ 46 → x ≠ 61 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) :=
  ⟨seg_init, icp_step, icp_exit, seg_icd, disp_end, seg_end, seg_pop, scan_exit, scan_head, dl_exit, dl_step, dd_far, dd_good, dd_up, dd_fi, up_exit, up_step, fi_step, fi_exit, seg_next, seg_good, scd_out, scd_tb⟩

end DetANN.HPIM.BD.SA

namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem _root_.solution :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 0) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 13).core.pc = off + 13 ∧ (run Q s detTape 13).halted = false ∧ (run Q s detTape 13).core.ptrs 14 = s.core.ptrs 14 - 2 * s.core.ptrs 1 ∧ (run Q s detTape 13).core.ptrs 40 = s.core.ptrs 13 ∧ (run Q s detTape 13).core.ptrs 43 = s.core.ptrs 14 - 2 * s.core.ptrs 1 ∧ (run Q s detTape 13).core.ptrs 46 = 0 ∧ (run Q s detTape 13).core.ptrs 60 = 2 * s.core.ptrs 1 ∧ (run Q s detTape 13).core.ptrs 68 = 1 ∧ (run Q s detTape 13).core.ptrs 69 = 0 ∧ (∀ x, x ≠ 14 → x ≠ 40 → x ≠ 43 → x ≠ 46 → x ≠ 60 → x ≠ 68 → x ≠ 69 → (run Q s detTape 13).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 13).core.regs 40 = (s.core.regs 11 * s.core.regs 11) ∧ (run Q s detTape 13).core.regs 41 = ((s.core.regs 12 * s.core.regs 11) * (s.core.regs 12 * s.core.regs 11)) ∧ (run Q s detTape 13).core.regs 47 = (s.core.regs 12 * s.core.regs 11) ∧ (run Q s detTape 13).core.regs 49 = (s.core.regs 11 + s.core.regs 11) ∧ (run Q s detTape 13).core.regs 50 = (0 : ℝ) ∧ (run Q s detTape 13).core.regs 53 = (2 : ℝ) ∧ (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 53 → (run Q s detTape 13).core.regs x = s.core.regs x) ∧ (run Q s detTape 13).core.mem = s.core.mem ∧ (run Q s detTape 13).integerMemory = s.integerMemory ∧ (run Q s detTape 13).work = s.work + 13 ∧ cellsWritten Q s 13 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State) (hpc : s.core.pc = off + 13) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 17 + s.core.ptrs 46) = x) (hb0 : s.core.ptrs 46 < s.core.ptrs 60) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 13 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 7).core.ptrs 50 = s.core.ptrs 43 + s.core.ptrs 46 ∧ (∀ x, x ≠ 46 → x ≠ 50 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs 55 = x ∧ (∀ x, x ≠ 55 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem (s.core.ptrs 43 + s.core.ptrs 46) = x ∧ (∀ z, z ≠ s.core.ptrs 43 + s.core.ptrs 46 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 43 + s.core.ptrs 46)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 13) (hh : s.halted = false) (hb0 : s.core.ptrs 60 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 20 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 20) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 14).core.pc = off + 34 ∧ (run Q s detTape 14).halted = false ∧ (run Q s detTape 14).core.ptrs 13 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 14).core.ptrs 42 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 14).core.ptrs 44 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 14).core.ptrs 57 = s.core.ptrs 13 - 2 ∧ (run Q s detTape 14).core.ptrs 59 = s.core.ptrs 13 - 1 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 44 → x ≠ 57 → x ≠ 59 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 43 ∧ (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 13 - 1 ∧ (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 40 ∧ (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 14).work = s.work + 14 ∧ ∀ c ∈ cellsWritten Q s 14, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hb0 : s.core.ptrs 40 ≤ s.core.ptrs 42) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 395 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (rt : ℤ) (s : State) (hpc : s.core.pc = off + 395) (hh : s.halted = false) (fi0 : s.integerMemory (s.core.ptrs 59) = rt) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 396 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs 17 = rt ∧ (∀ x, x ≠ 17 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (ep esl elink : ℤ) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (fi0 : s.integerMemory (s.core.ptrs 42) = ep) (fi1 : s.integerMemory (s.core.ptrs 42 + 1) = esl) (fi2 : s.integerMemory (s.core.ptrs 42 + 2) = elink) (hb0 : s.core.ptrs 42 < s.core.ptrs 40) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 11).core.pc = off + 45 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 14 = s.core.ptrs 14 - s.core.ptrs 60 ∧ (run Q s detTape 11).core.ptrs 42 = elink ∧ (run Q s detTape 11).core.ptrs 43 = ep ∧ (run Q s detTape 11).core.ptrs 44 = esl ∧ (run Q s detTape 11).core.ptrs 45 = 0 ∧ (run Q s detTape 11).core.ptrs 48 = s.core.ptrs 14 - s.core.ptrs 60 ∧ (run Q s detTape 11).core.ptrs 49 = 0 ∧ (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 42 + 2 ∧ (∀ x, x ≠ 14 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 48 → x ≠ 49 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).integerMemory = s.integerMemory ∧ (run Q s detTape 11).work = s.work + 11 ∧ cellsWritten Q s 11 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 45) (hh : s.halted = false) (hb0 : s.core.ptrs 11 ≤ s.core.ptrs 45) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 131 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (ki pa : ℤ) (s : State) (hpc : s.core.pc = off + 45) (hh : s.halted = false) (fi0 : s.integerMemory (s.core.ptrs 10 + s.core.ptrs 45) = ki) (fi1 : s.integerMemory (s.core.ptrs 12 + ki) = pa) (hb0 : s.core.ptrs 45 < s.core.ptrs 11) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 8).core.pc = off + 53 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 46 = 0 ∧ (run Q s detTape 8).core.ptrs 47 = pa ∧ (run Q s detTape 8).core.ptrs 57 = s.core.ptrs 12 + ki ∧ (∀ x, x ≠ 46 → x ≠ 47 → x ≠ 57 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs 42 = (0 : ℝ) ∧ (run Q s detTape 8).core.regs 43 = (0 : ℝ) ∧ (∀ x, x ≠ 42 → x ≠ 43 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).integerMemory = s.integerMemory ∧ (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 53) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 86 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x lo hi : ℝ) (s : State) (hpc : s.core.pc = off + 53) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x) (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo) (fr2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 33).core.pc = off + 53 ∧ (run Q s detTape 33).halted = false ∧ (run Q s detTape 33).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 33).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 33).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 33).core.regs 42 = (s.core.regs 42 + (((((lo - x) + (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) + Real.sqrt (((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) * ((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)))) / s.core.regs 53) * ((((lo - x) + (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) + Real.sqrt (((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)) * ((lo - x) - (((x - hi) + Real.sqrt ((x - hi) * (x - hi))) / s.core.regs 53)))) / s.core.regs 53))) ∧ (run Q s detTape 33).core.regs 43 = (s.core.regs 43 + (((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) * ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53))) ∧ (run Q s detTape 33).core.regs 44 = x ∧ (run Q s detTape 33).core.regs 45 = lo ∧ (run Q s detTape 33).core.regs 46 = hi ∧ (run Q s detTape 33).core.regs 47 = ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) ∧ (run Q s detTape 33).core.regs 48 = (hi - x) ∧ (run Q s detTape 33).core.regs 54 = (((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53) * ((((x - lo) + (hi - x)) + Real.sqrt (((x - lo) - (hi - x)) * ((x - lo) - (hi - x)))) / s.core.regs 53)) ∧ (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 54 → (run Q s detTape 33).core.regs x = s.core.regs x) ∧ (run Q s detTape 33).core.mem = s.core.mem ∧ (run Q s detTape 33).integerMemory = s.integerMemory ∧ (run Q s detTape 33).work = s.work + 33 ∧ cellsWritten Q s 33 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 86) (hh : s.halted = false) (hb0 : ¬ (s.core.regs 42 - s.core.regs 40) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 126 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs = s.core.ptrs ∧ (run Q s detTape 3).core.regs 54 = (s.core.regs 42 - s.core.regs 40) ∧ (∀ x, x ≠ 54 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 86) (hh : s.halted = false) (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0) (hb1 : (s.core.regs 43 - s.core.regs 41) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 4).core.pc = off + 128 ∧ (run Q s detTape 4).halted = false ∧ (run Q s detTape 4).core.ptrs = s.core.ptrs ∧ (run Q s detTape 4).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧ (∀ x, x ≠ 54 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧ (run Q s detTape 4).core.mem = s.core.mem ∧ (run Q s detTape 4).integerMemory = s.integerMemory ∧ (run Q s detTape 4).work = s.work + 4 ∧ cellsWritten Q s 4 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 86) (hh : s.halted = false) (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0) (hb1 : ¬ (s.core.regs 43 - s.core.regs 41) ≤ 0) (hb2 : s.core.ptrs 69 < s.core.ptrs 49) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 6).core.pc = off + 93 ∧ (run Q s detTape 6).halted = false ∧ (run Q s detTape 6).core.ptrs 46 = 0 ∧ (∀ x, x ≠ 46 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 6).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧ (∀ x, x ≠ 54 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧ (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).integerMemory = s.integerMemory ∧ (run Q s detTape 6).work = s.work + 6 ∧ cellsWritten Q s 6 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 86) (hh : s.halted = false) (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0) (hb1 : ¬ (s.core.regs 43 - s.core.regs 41) ≤ 0) (hb2 : s.core.ptrs 49 ≤ s.core.ptrs 69) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 6).core.pc = off + 116 ∧ (run Q s detTape 6).halted = false ∧ (run Q s detTape 6).core.ptrs 46 = 0 ∧ (∀ x, x ≠ 46 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 6).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧ (∀ x, x ≠ 54 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧ (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).integerMemory = s.integerMemory ∧ (run Q s detTape 6).work = s.work + 6 ∧ cellsWritten Q s 6 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 93) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 126 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x mn mx : ℝ) (s : State) (hpc : s.core.pc = off + 93) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x) (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn) (fr2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 23).core.pc = off + 93 ∧ (run Q s detTape 23).halted = false ∧ (run Q s detTape 23).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 23).core.regs 44 = x ∧ (run Q s detTape 23).core.regs 45 = mx ∧ (run Q s detTape 23).core.regs 47 = (((mx + x) + Real.sqrt ((mx - x) * (mx - x))) / s.core.regs 53) ∧ (run Q s detTape 23).core.regs 54 = Real.sqrt ((mx - x) * (mx - x)) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 23).core.regs x = s.core.regs x) ∧ (run Q s detTape 23).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = (((mn + x) - Real.sqrt ((mn - x) * (mn - x))) / s.core.regs 53) ∧ (run Q s detTape 23).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = (((mx + x) + Real.sqrt ((mx - x) * (mx - x))) / s.core.regs 53) ∧ (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 23).core.mem z = s.core.mem z) ∧ (run Q s detTape 23).integerMemory = s.integerMemory ∧ (run Q s detTape 23).work = s.work + 23 ∧ ∀ c ∈ cellsWritten Q s 23, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State) (hpc : s.core.pc = off + 116) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 47 + s.core.ptrs 46) = x) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 9).core.pc = off + 116 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 9).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs 44 = x ∧ (∀ x, x ≠ 44 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧ (run Q s detTape 9).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = x ∧ (run Q s detTape 9).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = x ∧ (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 116) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 2).core.pc = off + 126 ∧ (run Q s detTape 2).halted = false ∧ (run Q s detTape 2).core.ptrs 49 = 1 ∧ (∀ x, x ≠ 49 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 126) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 2).core.pc = off + 45 ∧ (run Q s detTape 2).halted = false ∧ (run Q s detTape 2).core.ptrs 45 = s.core.ptrs 45 + 1 ∧ (∀ x, x ≠ 45 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 128) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 383 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 61 = s.core.ptrs 45 + 1 ∧ (∀ x, x ≠ 61 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 131) (hh : s.halted = false) (hb0 : s.core.ptrs 49 ≤ s.core.ptrs 69) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 2).core.pc = off + 383 ∧ (run Q s detTape 2).halted = false ∧ (run Q s detTape 2).core.ptrs 61 = 0 ∧ (∀ x, x ≠ 61 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 131) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 49) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 134 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 46 = 0 ∧ (run Q s detTape 3).core.ptrs 61 = 0 ∧ (∀ x, x ≠ 46 → x ≠ 61 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) :=
  DetANN.HPIM.BD.SA.scan_steps'

end DetANN.HPIM.BD

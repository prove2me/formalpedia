-- Prove2me | solution 1 for DetANN.HPIM.BD.carve_steps
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T21:34:29.879118+00:00
-- url     : https://prove2.me/submissions/5b999d09-5a88-4128-ad76-e859ffad4051

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

lemma emb_cv {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_cv off) (off + 280) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE))))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, len_cs, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_cv2 {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_cv2 off) (off + 304) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE)))))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, len_cs, len_cv, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_cv3 {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_cv3 off) (off + 326) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE))))))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, len_cs, len_cv, len_cv2, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_cv4 {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_cv4 off) (off + 348) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE)))))))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, len_cs, len_cv, len_cv2, len_cv3, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_ce {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_ce off) (off + 372) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE))))))))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, len_cs, len_cv, len_cv2, len_cv3, len_cv4, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_leaf {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_leaf off) (off + 383) := by
  have h := embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE))))))))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, len_cs, len_cv, len_cv2, len_cv3, len_cv4, len_ce, Nat.add_assoc, Nat.reduceAdd] using h

end DetANN.HPIM.BD

-- ===== BD_PrfC =====
namespace DetANN.HPIM.BD.SC

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

variable {m n : ℕ}

lemma seg_carve (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 280) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 283 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 53 = 0 ∧
      (run Q s detTape 3).core.ptrs 54 = s.core.ptrs 43 ∧
      (run Q s detTape 3).core.ptrs 55 = s.core.ptrs 44 ∧
      (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_cv hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma ck_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 283) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 53)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 372 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_cv hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

lemma ck_nolow (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tl lo : ℝ) (s : State)
    (hpc : s.core.pc = off + 283) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53) = tl)
    (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53) = lo)
    (hb0 : s.core.ptrs 53 < s.core.ptrs 1)
    (hb1 : (tl - lo) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 326 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 54 + s.core.ptrs 53 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 44 = tl ∧
      (run Q s detTape 7).core.regs 45 = lo ∧
      (run Q s detTape 7).core.regs 54 = (tl - lo) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 54 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ := by
  have hS := emb_cv hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 48 + ptrs 53 → mem z = tl := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 54 + ptrs 53 → mem z = lo := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma ck_low (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tl lo : ℝ) (s : State)
    (hpc : s.core.pc = off + 283) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53) = tl)
    (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53) = lo)
    (hb0 : s.core.ptrs 53 < s.core.ptrs 1)
    (hb1 : ¬ (tl - lo) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 55) :
    (run Q s detTape 21).core.pc = off + 258 ∧
      (run Q s detTape 21).halted = false ∧
      (run Q s detTape 21).core.ptrs 13 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 21).core.ptrs 50 = s.core.ptrs 54 ∧
      (run Q s detTape 21).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧
      (run Q s detTape 21).core.ptrs 52 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 21).core.ptrs 57 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 21).core.ptrs 58 = 2 ∧
      (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 21).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 21).core.regs 44 = tl ∧
      (run Q s detTape 21).core.regs 45 = lo ∧
      (run Q s detTape 21).core.regs 54 = (tl - lo) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 54 → (run Q s detTape 21).core.regs x = s.core.regs x) ∧
      (run Q s detTape 21).core.mem = s.core.mem ∧
      (run Q s detTape 21).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧
      (run Q s detTape 21).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      (run Q s detTape 21).integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 55 → (run Q s detTape 21).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 21).work = s.work + 21 ∧
      ∀ c ∈ cellsWritten Q s 21, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 55) := by
  have hS := emb_cv hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 hm1 hx0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 48 + ptrs 53 → mem z = tl := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 54 + ptrs 53 → mem z = lo := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

lemma seg_r2 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 304) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 17).core.pc = off + 258 ∧
      (run Q s detTape 17).halted = false ∧
      (run Q s detTape 17).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 17).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 17).core.ptrs 50 = s.core.ptrs 54 ∧
      (run Q s detTape 17).core.ptrs 51 = s.core.ptrs 53 ∧
      (run Q s detTape 17).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 17).core.ptrs 58 = 3 ∧
      (run Q s detTape 17).core.ptrs 62 = s.core.ptrs 52 + 2 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 17).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 17).core.regs = s.core.regs ∧
      (run Q s detTape 17).core.mem = s.core.mem ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 2 ∧
      (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 17).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 17).work = s.work + 17 ∧
      ∀ c ∈ cellsWritten Q s 17, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) := by
  have hS := emb_cv2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

lemma seg_r3 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 321) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 5).core.pc = off + 326 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 54 = s.core.ptrs 56 ∧
      (run Q s detTape 5).core.ptrs 55 = s.core.ptrs 52 + 3 ∧
      (∀ x, x ≠ 54 → x ≠ 55 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := emb_cv2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma ch_nohigh (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (th hi : ℝ) (s : State)
    (hpc : s.core.pc = off + 326) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53 + s.core.ptrs 1) = th)
    (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1) = hi)
    (hb0 : (hi - th) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 8).core.pc = off + 370 ∧
      (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 57 = s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs 44 = th ∧
      (run Q s detTape 8).core.regs 46 = hi ∧
      (run Q s detTape 8).core.regs 54 = (hi - th) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧
      (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧
      cellsWritten Q s 8 = ∅ := by
  have hS := emb_cv3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 48 + ptrs 53 + ptrs 1 → mem z = th := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 54 + ptrs 53 + ptrs 1 → mem z = hi := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma ch_high (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (th hi : ℝ) (s : State)
    (hpc : s.core.pc = off + 326) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53 + s.core.ptrs 1) = th)
    (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1) = hi)
    (hb0 : ¬ (hi - th) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 55) :
    (run Q s detTape 22).core.pc = off + 258 ∧
      (run Q s detTape 22).halted = false ∧
      (run Q s detTape 22).core.ptrs 13 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 22).core.ptrs 50 = s.core.ptrs 54 ∧
      (run Q s detTape 22).core.ptrs 51 = s.core.ptrs 53 ∧
      (run Q s detTape 22).core.ptrs 52 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 22).core.ptrs 57 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 22).core.ptrs 58 = 4 ∧
      (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 22).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 22).core.regs 44 = th ∧
      (run Q s detTape 22).core.regs 46 = hi ∧
      (run Q s detTape 22).core.regs 54 = (hi - th) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → (run Q s detTape 22).core.regs x = s.core.regs x) ∧
      (run Q s detTape 22).core.mem = s.core.mem ∧
      (run Q s detTape 22).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧
      (run Q s detTape 22).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      (run Q s detTape 22).integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 55 → (run Q s detTape 22).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 22).work = s.work + 22 ∧
      ∀ c ∈ cellsWritten Q s 22, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 55) := by
  have hS := emb_cv3 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hm1 hx0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 48 + ptrs 53 + ptrs 1 → mem z = th := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 54 + ptrs 53 + ptrs 1 → mem z = hi := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

lemma seg_r4 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 348) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 18).core.pc = off + 258 ∧
      (run Q s detTape 18).halted = false ∧
      (run Q s detTape 18).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 18).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 18).core.ptrs 50 = s.core.ptrs 54 ∧
      (run Q s detTape 18).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧
      (run Q s detTape 18).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 18).core.ptrs 58 = 5 ∧
      (run Q s detTape 18).core.ptrs 62 = s.core.ptrs 52 + 3 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 18).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 18).core.regs = s.core.regs ∧
      (run Q s detTape 18).core.mem = s.core.mem ∧
      (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧
      (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 3 ∧
      (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 18).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 18).work = s.work + 18 ∧
      ∀ c ∈ cellsWritten Q s 18, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) := by
  have hS := emb_cv4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

lemma seg_r5 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 366) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 6).core.pc = off + 283 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 53 = s.core.ptrs 53 + 1 ∧
      (run Q s detTape 6).core.ptrs 54 = s.core.ptrs 56 ∧
      (run Q s detTape 6).core.ptrs 55 = s.core.ptrs 52 + 2 ∧
      (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs = s.core.regs ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ := by
  have hS := emb_cv4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma seg_cn (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 370) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 2).core.pc = off + 283 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 53 = s.core.ptrs 53 + 1 ∧
      (∀ x, x ≠ 53 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ := by
  have hS := emb_cv4 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma seg_ce (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 372) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 11).core.pc = off + 34 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 11).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs = s.core.regs ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 55 ∧
      (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      ∀ c ∈ cellsWritten Q s 11, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) := by
  have hS := emb_ce hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

lemma seg_leaf (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 383) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 44) :
    (run Q s detTape 12).core.pc = off + 34 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 12).core.ptrs 52 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 12).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (∀ x, x ≠ 13 → x ≠ 52 → x ≠ 57 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs = s.core.regs ∧
      (run Q s detTape 12).core.mem = s.core.mem ∧
      (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 69 ∧
      (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 43 ∧
      (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 61 ∧
      (run Q s detTape 12).integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 3 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → z ≠ s.core.ptrs 44 → (run Q s detTape 12).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      ∀ c ∈ cellsWritten Q s 12, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) ∨ c = (false, s.core.ptrs 44) := by
  have hS := emb_leaf hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 hx0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h | h <;> subst h <;> simp <;> omega)⟩

theorem carve_steps' :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 280) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 283 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 53 = 0 ∧ (run Q s detTape 3).core.ptrs 54 = s.core.ptrs 43 ∧ (run Q s detTape 3).core.ptrs 55 = s.core.ptrs 44 ∧ (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 53) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 372 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tl lo : ℝ) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53) = tl) (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53) = lo) (hb0 : s.core.ptrs 53 < s.core.ptrs 1) (hb1 : (tl - lo) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 326 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 54 + s.core.ptrs 53 ∧ (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs 44 = tl ∧ (run Q s detTape 7).core.regs 45 = lo ∧ (run Q s detTape 7).core.regs 54 = (tl - lo) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 54 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tl lo : ℝ) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53) = tl) (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53) = lo) (hb0 : s.core.ptrs 53 < s.core.ptrs 1) (hb1 : ¬ (tl - lo) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 55),
      (run Q s detTape 21).core.pc = off + 258 ∧ (run Q s detTape 21).halted = false ∧ (run Q s detTape 21).core.ptrs 13 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 21).core.ptrs 50 = s.core.ptrs 54 ∧ (run Q s detTape 21).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧ (run Q s detTape 21).core.ptrs 52 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 21).core.ptrs 57 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 21).core.ptrs 58 = 2 ∧ (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 21).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 21).core.regs 44 = tl ∧ (run Q s detTape 21).core.regs 45 = lo ∧ (run Q s detTape 21).core.regs 54 = (tl - lo) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 54 → (run Q s detTape 21).core.regs x = s.core.regs x) ∧ (run Q s detTape 21).core.mem = s.core.mem ∧ (run Q s detTape 21).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧ (run Q s detTape 21).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ (run Q s detTape 21).integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 55 → (run Q s detTape 21).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 21).work = s.work + 21 ∧ ∀ c ∈ cellsWritten Q s 21, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 55)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 304) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 17).core.pc = off + 258 ∧ (run Q s detTape 17).halted = false ∧ (run Q s detTape 17).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 17).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 17).core.ptrs 50 = s.core.ptrs 54 ∧ (run Q s detTape 17).core.ptrs 51 = s.core.ptrs 53 ∧ (run Q s detTape 17).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 17).core.ptrs 58 = 3 ∧ (run Q s detTape 17).core.ptrs 62 = s.core.ptrs 52 + 2 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 17).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 17).core.regs = s.core.regs ∧ (run Q s detTape 17).core.mem = s.core.mem ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 2 ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 17).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 17).work = s.work + 17 ∧ ∀ c ∈ cellsWritten Q s 17, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 321) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 5).core.pc = off + 326 ∧ (run Q s detTape 5).halted = false ∧ (run Q s detTape 5).core.ptrs 54 = s.core.ptrs 56 ∧ (run Q s detTape 5).core.ptrs 55 = s.core.ptrs 52 + 3 ∧ (∀ x, x ≠ 54 → x ≠ 55 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 5).core.regs = s.core.regs ∧ (run Q s detTape 5).core.mem = s.core.mem ∧ (run Q s detTape 5).integerMemory = s.integerMemory ∧ (run Q s detTape 5).work = s.work + 5 ∧ cellsWritten Q s 5 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (th hi : ℝ) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53 + s.core.ptrs 1) = th) (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1) = hi) (hb0 : (hi - th) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 8).core.pc = off + 370 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 57 = s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1 ∧ (∀ x, x ≠ 57 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs 44 = th ∧ (run Q s detTape 8).core.regs 46 = hi ∧ (run Q s detTape 8).core.regs 54 = (hi - th) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).integerMemory = s.integerMemory ∧ (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (th hi : ℝ) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53 + s.core.ptrs 1) = th) (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1) = hi) (hb0 : ¬ (hi - th) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 55),
      (run Q s detTape 22).core.pc = off + 258 ∧ (run Q s detTape 22).halted = false ∧ (run Q s detTape 22).core.ptrs 13 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 22).core.ptrs 50 = s.core.ptrs 54 ∧ (run Q s detTape 22).core.ptrs 51 = s.core.ptrs 53 ∧ (run Q s detTape 22).core.ptrs 52 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 22).core.ptrs 57 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 22).core.ptrs 58 = 4 ∧ (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 22).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 22).core.regs 44 = th ∧ (run Q s detTape 22).core.regs 46 = hi ∧ (run Q s detTape 22).core.regs 54 = (hi - th) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → (run Q s detTape 22).core.regs x = s.core.regs x) ∧ (run Q s detTape 22).core.mem = s.core.mem ∧ (run Q s detTape 22).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧ (run Q s detTape 22).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ (run Q s detTape 22).integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 55 → (run Q s detTape 22).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 22).work = s.work + 22 ∧ ∀ c ∈ cellsWritten Q s 22, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 55)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 348) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 18).core.pc = off + 258 ∧ (run Q s detTape 18).halted = false ∧ (run Q s detTape 18).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 18).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 18).core.ptrs 50 = s.core.ptrs 54 ∧ (run Q s detTape 18).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧ (run Q s detTape 18).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 18).core.ptrs 58 = 5 ∧ (run Q s detTape 18).core.ptrs 62 = s.core.ptrs 52 + 3 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 18).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 18).core.regs = s.core.regs ∧ (run Q s detTape 18).core.mem = s.core.mem ∧ (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧ (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 3 ∧ (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 18).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 18).work = s.work + 18 ∧ ∀ c ∈ cellsWritten Q s 18, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 366) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 6).core.pc = off + 283 ∧ (run Q s detTape 6).halted = false ∧ (run Q s detTape 6).core.ptrs 53 = s.core.ptrs 53 + 1 ∧ (run Q s detTape 6).core.ptrs 54 = s.core.ptrs 56 ∧ (run Q s detTape 6).core.ptrs 55 = s.core.ptrs 52 + 2 ∧ (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 6).core.regs = s.core.regs ∧ (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).integerMemory = s.integerMemory ∧ (run Q s detTape 6).work = s.work + 6 ∧ cellsWritten Q s 6 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 370) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 2).core.pc = off + 283 ∧ (run Q s detTape 2).halted = false ∧ (run Q s detTape 2).core.ptrs 53 = s.core.ptrs 53 + 1 ∧ (∀ x, x ≠ 53 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 372) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 11).core.pc = off + 34 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 11).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 55 ∧ (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 11).work = s.work + 11 ∧ ∀ c ∈ cellsWritten Q s 11, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 383) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 44),
      (run Q s detTape 12).core.pc = off + 34 ∧ (run Q s detTape 12).halted = false ∧ (run Q s detTape 12).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 12).core.ptrs 52 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 12).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (∀ x, x ≠ 13 → x ≠ 52 → x ≠ 57 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 12).core.regs = s.core.regs ∧ (run Q s detTape 12).core.mem = s.core.mem ∧ (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 69 ∧ (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 43 ∧ (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 61 ∧ (run Q s detTape 12).integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 3 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → z ≠ s.core.ptrs 44 → (run Q s detTape 12).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 12).work = s.work + 12 ∧ ∀ c ∈ cellsWritten Q s 12, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) ∨ c = (false, s.core.ptrs 44)) :=
  ⟨seg_carve, ck_exit, ck_nolow, ck_low, seg_r2, seg_r3, ch_nohigh, ch_high, seg_r4, seg_r5, seg_cn, seg_ce, seg_leaf⟩

end DetANN.HPIM.BD.SC

namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem _root_.solution :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 280) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 283 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 53 = 0 ∧ (run Q s detTape 3).core.ptrs 54 = s.core.ptrs 43 ∧ (run Q s detTape 3).core.ptrs 55 = s.core.ptrs 44 ∧ (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 53) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 372 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tl lo : ℝ) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53) = tl) (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53) = lo) (hb0 : s.core.ptrs 53 < s.core.ptrs 1) (hb1 : (tl - lo) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 326 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 54 + s.core.ptrs 53 ∧ (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs 44 = tl ∧ (run Q s detTape 7).core.regs 45 = lo ∧ (run Q s detTape 7).core.regs 54 = (tl - lo) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 54 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tl lo : ℝ) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53) = tl) (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53) = lo) (hb0 : s.core.ptrs 53 < s.core.ptrs 1) (hb1 : ¬ (tl - lo) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 55),
      (run Q s detTape 21).core.pc = off + 258 ∧ (run Q s detTape 21).halted = false ∧ (run Q s detTape 21).core.ptrs 13 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 21).core.ptrs 50 = s.core.ptrs 54 ∧ (run Q s detTape 21).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧ (run Q s detTape 21).core.ptrs 52 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 21).core.ptrs 57 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 21).core.ptrs 58 = 2 ∧ (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 21).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 21).core.regs 44 = tl ∧ (run Q s detTape 21).core.regs 45 = lo ∧ (run Q s detTape 21).core.regs 54 = (tl - lo) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 54 → (run Q s detTape 21).core.regs x = s.core.regs x) ∧ (run Q s detTape 21).core.mem = s.core.mem ∧ (run Q s detTape 21).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧ (run Q s detTape 21).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ (run Q s detTape 21).integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 55 → (run Q s detTape 21).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 21).work = s.work + 21 ∧ ∀ c ∈ cellsWritten Q s 21, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 55)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 304) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 17).core.pc = off + 258 ∧ (run Q s detTape 17).halted = false ∧ (run Q s detTape 17).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 17).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 17).core.ptrs 50 = s.core.ptrs 54 ∧ (run Q s detTape 17).core.ptrs 51 = s.core.ptrs 53 ∧ (run Q s detTape 17).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 17).core.ptrs 58 = 3 ∧ (run Q s detTape 17).core.ptrs 62 = s.core.ptrs 52 + 2 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 17).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 17).core.regs = s.core.regs ∧ (run Q s detTape 17).core.mem = s.core.mem ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 2 ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 17).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 17).work = s.work + 17 ∧ ∀ c ∈ cellsWritten Q s 17, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 321) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 5).core.pc = off + 326 ∧ (run Q s detTape 5).halted = false ∧ (run Q s detTape 5).core.ptrs 54 = s.core.ptrs 56 ∧ (run Q s detTape 5).core.ptrs 55 = s.core.ptrs 52 + 3 ∧ (∀ x, x ≠ 54 → x ≠ 55 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 5).core.regs = s.core.regs ∧ (run Q s detTape 5).core.mem = s.core.mem ∧ (run Q s detTape 5).integerMemory = s.integerMemory ∧ (run Q s detTape 5).work = s.work + 5 ∧ cellsWritten Q s 5 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (th hi : ℝ) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53 + s.core.ptrs 1) = th) (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1) = hi) (hb0 : (hi - th) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 8).core.pc = off + 370 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 57 = s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1 ∧ (∀ x, x ≠ 57 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs 44 = th ∧ (run Q s detTape 8).core.regs 46 = hi ∧ (run Q s detTape 8).core.regs 54 = (hi - th) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).integerMemory = s.integerMemory ∧ (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (th hi : ℝ) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53 + s.core.ptrs 1) = th) (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1) = hi) (hb0 : ¬ (hi - th) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 55),
      (run Q s detTape 22).core.pc = off + 258 ∧ (run Q s detTape 22).halted = false ∧ (run Q s detTape 22).core.ptrs 13 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 22).core.ptrs 50 = s.core.ptrs 54 ∧ (run Q s detTape 22).core.ptrs 51 = s.core.ptrs 53 ∧ (run Q s detTape 22).core.ptrs 52 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 22).core.ptrs 57 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 22).core.ptrs 58 = 4 ∧ (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 22).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 22).core.regs 44 = th ∧ (run Q s detTape 22).core.regs 46 = hi ∧ (run Q s detTape 22).core.regs 54 = (hi - th) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → (run Q s detTape 22).core.regs x = s.core.regs x) ∧ (run Q s detTape 22).core.mem = s.core.mem ∧ (run Q s detTape 22).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧ (run Q s detTape 22).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ (run Q s detTape 22).integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 55 → (run Q s detTape 22).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 22).work = s.work + 22 ∧ ∀ c ∈ cellsWritten Q s 22, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 55)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 348) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 18).core.pc = off + 258 ∧ (run Q s detTape 18).halted = false ∧ (run Q s detTape 18).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 18).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 18).core.ptrs 50 = s.core.ptrs 54 ∧ (run Q s detTape 18).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧ (run Q s detTape 18).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 18).core.ptrs 58 = 5 ∧ (run Q s detTape 18).core.ptrs 62 = s.core.ptrs 52 + 3 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 18).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 18).core.regs = s.core.regs ∧ (run Q s detTape 18).core.mem = s.core.mem ∧ (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧ (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 3 ∧ (run Q s detTape 18).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 18).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 18).work = s.work + 18 ∧ ∀ c ∈ cellsWritten Q s 18, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 366) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 6).core.pc = off + 283 ∧ (run Q s detTape 6).halted = false ∧ (run Q s detTape 6).core.ptrs 53 = s.core.ptrs 53 + 1 ∧ (run Q s detTape 6).core.ptrs 54 = s.core.ptrs 56 ∧ (run Q s detTape 6).core.ptrs 55 = s.core.ptrs 52 + 2 ∧ (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 6).core.regs = s.core.regs ∧ (run Q s detTape 6).core.mem = s.core.mem ∧ (run Q s detTape 6).integerMemory = s.integerMemory ∧ (run Q s detTape 6).work = s.work + 6 ∧ cellsWritten Q s 6 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 370) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 2).core.pc = off + 283 ∧ (run Q s detTape 2).halted = false ∧ (run Q s detTape 2).core.ptrs 53 = s.core.ptrs 53 + 1 ∧ (∀ x, x ≠ 53 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 372) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 11).core.pc = off + 34 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 11).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 55 ∧ (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 11).work = s.work + 11 ∧ ∀ c ∈ cellsWritten Q s 11, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 383) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 44),
      (run Q s detTape 12).core.pc = off + 34 ∧ (run Q s detTape 12).halted = false ∧ (run Q s detTape 12).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 12).core.ptrs 52 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 12).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (∀ x, x ≠ 13 → x ≠ 52 → x ≠ 57 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 12).core.regs = s.core.regs ∧ (run Q s detTape 12).core.mem = s.core.mem ∧ (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 69 ∧ (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 43 ∧ (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 61 ∧ (run Q s detTape 12).integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 3 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → z ≠ s.core.ptrs 44 → (run Q s detTape 12).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 12).work = s.work + 12 ∧ ∀ c ∈ cellsWritten Q s 12, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) ∨ c = (false, s.core.ptrs 44)) :=
  DetANN.HPIM.BD.SC.carve_steps'

end DetANN.HPIM.BD

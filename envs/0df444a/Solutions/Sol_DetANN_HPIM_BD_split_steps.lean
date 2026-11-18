-- Prove2me | solution 1 for DetANN.HPIM.BD.split_steps
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T21:34:28.890489+00:00
-- url     : https://prove2.me/submissions/263b4eba-42c5-414b-814e-814573d9af4a

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

lemma emb_tb {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_tb off) (off + 134) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_sg0 {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_sg0 off) (off + 161) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE)))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_sg {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_sg off) (off + 172) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_split {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_split off) (off + 197) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE)))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_split2 {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_split2 off) (off + 226) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, Nat.add_assoc, Nat.reduceAdd] using h

lemma emb_cs {Q : Program} {off : ℕ} (hE : Embeds Q (bd off) off) : Embeds Q (bd_cs off) (off + 258) := by
  have h := embeds_app_left (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (embeds_app_right (hE)))))))))))
  simpa only [len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, Nat.add_assoc, Nat.reduceAdd] using h

end DetANN.HPIM.BD

-- ===== BD_PrfB =====
namespace DetANN.HPIM.BD.SB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

variable {m n : ℕ}

lemma tb_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 134) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 161 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_tb hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- One coordinate of the tight box. -/
lemma tb_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (mn lo mx hi : ℝ) (s : State)
    (hpc : s.core.pc = off + 134) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn)
    (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo)
    (fr2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx)
    (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 48 < s.core.ptrs 43) :
    (run Q s detTape 27).core.pc = off + 134 ∧
      (run Q s detTape 27).halted = false ∧
      (run Q s detTape 27).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 27).core.ptrs 50 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (run Q s detTape 27).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → (run Q s detTape 27).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 27).core.regs 44 = (mx + s.core.regs 49) ∧
      (run Q s detTape 27).core.regs 45 = hi ∧
      (run Q s detTape 27).core.regs 47 = ((((mx + s.core.regs 49) + hi) - Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi))) / s.core.regs 53) ∧
      (run Q s detTape 27).core.regs 54 = Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi)) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 27).core.regs x = s.core.regs x) ∧
      (run Q s detTape 27).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = ((((mn - s.core.regs 49) + lo) + Real.sqrt (((mn - s.core.regs 49) - lo) * ((mn - s.core.regs 49) - lo))) / s.core.regs 53) ∧
      (run Q s detTape 27).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = ((((mx + s.core.regs 49) + hi) - Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi))) / s.core.regs 53) ∧
      (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 27).core.mem z = s.core.mem z) ∧
      (run Q s detTape 27).integerMemory = s.integerMemory ∧
      (run Q s detTape 27).work = s.work + 27 ∧
      ∀ c ∈ cellsWritten Q s 27, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) := by
  have hS := emb_tb hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 fr2 fr3 hb0 hm1 hx0 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 48 + ptrs 46 → mem z = mn := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 43 + ptrs 46 → mem z = lo := fun z hz => hz ▸ fr1
  have er2 : ∀ z, z = ptrs 48 + ptrs 46 + ptrs 1 → mem z = mx := fun z hz => hz ▸ fr2
  have er3 : ∀ z, z = ptrs 43 + ptrs 46 + ptrs 1 → mem z = hi := fun z hz => hz ▸ fr3
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h <;> subst h <;> simp <;> omega)⟩

lemma seg_sg0 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a0 b0 c0 d0 : ℝ) (s : State)
    (hpc : s.core.pc = off + 161) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48) = a0)
    (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 1) = b0)
    (fr2 : s.core.mem (s.core.ptrs 43) = c0)
    (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 1) = d0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 11).core.pc = off + 172 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 46 = 1 ∧
      (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs 44 = c0 ∧
      (run Q s detTape 11).core.regs 45 = d0 ∧
      (run Q s detTape 11).core.regs 51 = (b0 - a0) ∧
      (run Q s detTape 11).core.regs 52 = (d0 - c0) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 51 → x ≠ 52 → (run Q s detTape 11).core.regs x = s.core.regs x) ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      cellsWritten Q s 11 = ∅ := by
  have hS := emb_sg0 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 fr2 fr3 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 48 → mem z = a0 := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 48 + ptrs 1 → mem z = b0 := fun z hz => hz ▸ fr1
  have er2 : ∀ z, z = ptrs 43 → mem z = c0 := fun z hz => hz ▸ fr2
  have er3 : ∀ z, z = ptrs 43 + ptrs 1 → mem z = d0 := fun z hz => hz ▸ fr3
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma sg_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 172) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 197 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_sg hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

/-- One coordinate of both longest sides. -/
lemma sg_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b c d : ℝ) (s : State)
    (hpc : s.core.pc = off + 172) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = a)
    (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = b)
    (fr2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = c)
    (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = d)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 25).core.pc = off + 172 ∧
      (run Q s detTape 25).halted = false ∧
      (run Q s detTape 25).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 25).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 25).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 25).core.regs 44 = c ∧
      (run Q s detTape 25).core.regs 45 = d ∧
      (run Q s detTape 25).core.regs 47 = (d - c) ∧
      (run Q s detTape 25).core.regs 51 = (((s.core.regs 51 + (b - a)) + Real.sqrt ((s.core.regs 51 - (b - a)) * (s.core.regs 51 - (b - a)))) / s.core.regs 53) ∧
      (run Q s detTape 25).core.regs 52 = (((s.core.regs 52 + (d - c)) + Real.sqrt ((s.core.regs 52 - (d - c)) * (s.core.regs 52 - (d - c)))) / s.core.regs 53) ∧
      (run Q s detTape 25).core.regs 54 = Real.sqrt ((s.core.regs 52 - (d - c)) * (s.core.regs 52 - (d - c))) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 51 → x ≠ 52 → x ≠ 54 → (run Q s detTape 25).core.regs x = s.core.regs x) ∧
      (run Q s detTape 25).core.mem = s.core.mem ∧
      (run Q s detTape 25).integerMemory = s.integerMemory ∧
      (run Q s detTape 25).work = s.work + 25 ∧
      cellsWritten Q s 25 = ∅ := by
  have hS := emb_sg hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 fr2 fr3 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 48 + ptrs 46 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 48 + ptrs 46 + ptrs 1 → mem z = b := fun z hz => hz ▸ fr1
  have er2 : ∀ z, z = ptrs 43 + ptrs 46 → mem z = c := fun z hz => hz ▸ fr2
  have er3 : ∀ z, z = ptrs 43 + ptrs 46 + ptrs 1 → mem z = d := fun z hz => hz ▸ fr3
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1, er2, er3]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma sgd_carve (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 197) (hh : s.halted = false)
    (hb0 : ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 280 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 3).core.regs 54 = ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_split hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma sgd_split (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 197) (hh : s.halted = false)
    (hb0 : ¬ ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 4).core.pc = off + 201 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 53 = 0 ∧
      (∀ x, x ≠ 53 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs 54 = ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ := by
  have hS := emb_split hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma la_next (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 201) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = a)
    (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = b)
    (hb0 : ¬ (s.core.regs 52 - (b - a)) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 9).core.pc = off + 201 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 53 = s.core.ptrs 53 + 1 ∧
      (run Q s detTape 9).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 53 → x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs 44 = a ∧
      (run Q s detTape 9).core.regs 45 = b ∧
      (run Q s detTape 9).core.regs 47 = (b - a) ∧
      (run Q s detTape 9).core.regs 54 = (s.core.regs 52 - (b - a)) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧
      (run Q s detTape 9).core.mem = s.core.mem ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      cellsWritten Q s 9 = ∅ := by
  have hS := emb_split hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 43 + ptrs 53 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 43 + ptrs 53 + ptrs 1 → mem z = b := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma la_found (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b : ℝ) (s : State)
    (hpc : s.core.pc = off + 201) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = a)
    (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = b)
    (hb0 : (s.core.regs 52 - (b - a)) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 210 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 44 = a ∧
      (run Q s detTape 7).core.regs 45 = b ∧
      (run Q s detTape 7).core.regs 47 = (b - a) ∧
      (run Q s detTape 7).core.regs 54 = (s.core.regs 52 - (b - a)) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ := by
  have hS := emb_split hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 fr1 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 43 + ptrs 53 → mem z = a := fun z hz => hz ▸ fr0
  have er1 : ∀ z, z = ptrs 43 + ptrs 53 + ptrs 1 → mem z = b := fun z hz => hz ▸ fr1
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0, er1]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

/-- The split node; copy for the left half. -/
lemma seg_laf (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 210) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 44) :
    (run Q s detTape 16).core.pc = off + 258 ∧
      (run Q s detTape 16).halted = false ∧
      (run Q s detTape 16).core.ptrs 13 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 43 ∧
      (run Q s detTape 16).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧
      (run Q s detTape 16).core.ptrs 52 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 16).core.ptrs 57 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 16).core.ptrs 58 = 0 ∧
      (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 16).core.regs 44 = ((s.core.regs 44 + s.core.regs 45) / s.core.regs 53) ∧
      (∀ x, x ≠ 44 → (run Q s detTape 16).core.regs x = s.core.regs x) ∧
      (run Q s detTape 16).core.mem = s.core.mem ∧
      (run Q s detTape 16).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧
      (run Q s detTape 16).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧
      (run Q s detTape 16).integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 44 → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 16).work = s.work + 16 ∧
      ∀ c ∈ cellsWritten Q s 16, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 44) := by
  have hS := emb_split hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 hx0 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

/-- Push the left half; copy for the right half. -/
lemma seg_r0 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 226) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 17).core.pc = off + 258 ∧
      (run Q s detTape 17).halted = false ∧
      (run Q s detTape 17).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 17).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 17).core.ptrs 50 = s.core.ptrs 43 ∧
      (run Q s detTape 17).core.ptrs 51 = s.core.ptrs 53 ∧
      (run Q s detTape 17).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 17).core.ptrs 58 = 1 ∧
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
  have hS := emb_split2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

/-- Push the right half. -/
lemma seg_r1 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 243) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 15).core.pc = off + 34 ∧
      (run Q s detTape 15).halted = false ∧
      (run Q s detTape 15).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 15).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 15).core.ptrs 62 = s.core.ptrs 52 + 3 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → x ≠ 62 → (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 15).core.regs = s.core.regs ∧
      (run Q s detTape 15).core.mem = s.core.mem ∧
      (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧
      (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 3 ∧
      (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 15).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 15).work = s.work + 15 ∧
      ∀ c ∈ cellsWritten Q s 15, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) := by
  have hS := emb_split2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; rcases hc with h | h | h <;> subst h <;> simp <;> omega)⟩

lemma cs_head (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 258) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 261 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 14 = s.core.ptrs 14 - s.core.ptrs 60 ∧
      (run Q s detTape 3).core.ptrs 46 = 0 ∧
      (run Q s detTape 3).core.ptrs 56 = s.core.ptrs 14 - s.core.ptrs 60 ∧
      (∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma cl_step (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State)
    (hpc : s.core.pc = off + 261) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 50 + s.core.ptrs 46) = x)
    (hb0 : s.core.ptrs 46 < s.core.ptrs 60)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 261 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 46 = s.core.ptrs 46 + 1 ∧
      (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 56 + s.core.ptrs 46 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 55 = x ∧
      (∀ x, x ≠ 55 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem (s.core.ptrs 56 + s.core.ptrs 46) = x ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 46 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 56 + s.core.ptrs 46) := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh fr0 hb0 hm1 ⊢
  subst hh
  have er0 : ∀ z, z = ptrs 50 + ptrs 46 → mem z = x := fun z hz => hz ▸ fr0
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  simp (disch := omega) only [er0]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma cl_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 261) (hh : s.halted = false)
    (hb0 : s.core.ptrs 60 ≤ s.core.ptrs 46)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 268 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by simp)⟩

lemma cd_0 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 58 ≤ s.core.ptrs 69)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 226 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 57 = s.core.ptrs 56 + s.core.ptrs 51 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 3).core.mem z = s.core.mem z) ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      ∀ c ∈ cellsWritten Q s 3, c = (true, s.core.ptrs 56 + s.core.ptrs 51) := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma cd_1 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : s.core.ptrs 58 ≤ 1)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 5).core.pc = off + 243 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 57 = 1 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 56 + s.core.ptrs 51) := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma cd_2 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : 1 < s.core.ptrs 58)
    (hb2 : s.core.ptrs 58 ≤ 2)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 304 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 57 = 2 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs = s.core.regs ∧
      (run Q s detTape 7).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 56 + s.core.ptrs 51) := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 hb2 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma cd_3 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : 1 < s.core.ptrs 58)
    (hb2 : 2 < s.core.ptrs 58)
    (hb3 : s.core.ptrs 58 ≤ 3)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 9).core.pc = off + 321 ∧
      (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 57 = 3 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs = s.core.regs ∧
      (run Q s detTape 9).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧
      ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 56 + s.core.ptrs 51) := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 hb2 hb3 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma cd_4 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : 1 < s.core.ptrs 58)
    (hb2 : 2 < s.core.ptrs 58)
    (hb3 : 3 < s.core.ptrs 58)
    (hb4 : s.core.ptrs 58 ≤ 4)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 11).core.pc = off + 348 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 57 = 4 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs = s.core.regs ∧
      (run Q s detTape 11).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 11).core.mem z = s.core.mem z) ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      ∀ c ∈ cellsWritten Q s 11, c = (true, s.core.ptrs 56 + s.core.ptrs 51) := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 hb2 hb3 hb4 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma cd_5 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 268) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 58)
    (hb1 : 1 < s.core.ptrs 58)
    (hb2 : 2 < s.core.ptrs 58)
    (hb3 : 3 < s.core.ptrs 58)
    (hb4 : 4 < s.core.ptrs 58)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 12).core.pc = off + 366 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 57 = 4 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs = s.core.regs ∧
      (run Q s detTape 12).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧
      (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 12).core.mem z = s.core.mem z) ∧
      (run Q s detTape 12).integerMemory = s.integerMemory ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      ∀ c ∈ cellsWritten Q s 12, c = (true, s.core.ptrs 56 + s.core.ptrs 51) := by
  have hS := emb_cs hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 hb1 hb2 hb3 hb4 hm1 ⊢
  subst hh
  rw [hpc]
  (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [run_exec_seg hS rfl rfl rfl rfl, cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [run_zero, cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

theorem split_steps' :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 134) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 161 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (mn lo mx hi : ℝ) (s : State) (hpc : s.core.pc = off + 134) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn) (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo) (fr2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx) (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 48 < s.core.ptrs 43),
      (run Q s detTape 27).core.pc = off + 134 ∧ (run Q s detTape 27).halted = false ∧ (run Q s detTape 27).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 27).core.ptrs 50 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (run Q s detTape 27).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → (run Q s detTape 27).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 27).core.regs 44 = (mx + s.core.regs 49) ∧ (run Q s detTape 27).core.regs 45 = hi ∧ (run Q s detTape 27).core.regs 47 = ((((mx + s.core.regs 49) + hi) - Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi))) / s.core.regs 53) ∧ (run Q s detTape 27).core.regs 54 = Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi)) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 27).core.regs x = s.core.regs x) ∧ (run Q s detTape 27).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = ((((mn - s.core.regs 49) + lo) + Real.sqrt (((mn - s.core.regs 49) - lo) * ((mn - s.core.regs 49) - lo))) / s.core.regs 53) ∧ (run Q s detTape 27).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = ((((mx + s.core.regs 49) + hi) - Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi))) / s.core.regs 53) ∧ (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 27).core.mem z = s.core.mem z) ∧ (run Q s detTape 27).integerMemory = s.integerMemory ∧ (run Q s detTape 27).work = s.work + 27 ∧ ∀ c ∈ cellsWritten Q s 27, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a0 b0 c0 d0 : ℝ) (s : State) (hpc : s.core.pc = off + 161) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48) = a0) (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 1) = b0) (fr2 : s.core.mem (s.core.ptrs 43) = c0) (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 1) = d0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 11).core.pc = off + 172 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 46 = 1 ∧ (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs 44 = c0 ∧ (run Q s detTape 11).core.regs 45 = d0 ∧ (run Q s detTape 11).core.regs 51 = (b0 - a0) ∧ (run Q s detTape 11).core.regs 52 = (d0 - c0) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 51 → x ≠ 52 → (run Q s detTape 11).core.regs x = s.core.regs x) ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).integerMemory = s.integerMemory ∧ (run Q s detTape 11).work = s.work + 11 ∧ cellsWritten Q s 11 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 172) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 197 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b c d : ℝ) (s : State) (hpc : s.core.pc = off + 172) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = a) (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = b) (fr2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = c) (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = d) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 25).core.pc = off + 172 ∧ (run Q s detTape 25).halted = false ∧ (run Q s detTape 25).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 25).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 25).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 25).core.regs 44 = c ∧ (run Q s detTape 25).core.regs 45 = d ∧ (run Q s detTape 25).core.regs 47 = (d - c) ∧ (run Q s detTape 25).core.regs 51 = (((s.core.regs 51 + (b - a)) + Real.sqrt ((s.core.regs 51 - (b - a)) * (s.core.regs 51 - (b - a)))) / s.core.regs 53) ∧ (run Q s detTape 25).core.regs 52 = (((s.core.regs 52 + (d - c)) + Real.sqrt ((s.core.regs 52 - (d - c)) * (s.core.regs 52 - (d - c)))) / s.core.regs 53) ∧ (run Q s detTape 25).core.regs 54 = Real.sqrt ((s.core.regs 52 - (d - c)) * (s.core.regs 52 - (d - c))) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 51 → x ≠ 52 → x ≠ 54 → (run Q s detTape 25).core.regs x = s.core.regs x) ∧ (run Q s detTape 25).core.mem = s.core.mem ∧ (run Q s detTape 25).integerMemory = s.integerMemory ∧ (run Q s detTape 25).work = s.work + 25 ∧ cellsWritten Q s 25 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hb0 : ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 280 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs = s.core.ptrs ∧ (run Q s detTape 3).core.regs 54 = ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ∧ (∀ x, x ≠ 54 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hb0 : ¬ ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 4).core.pc = off + 201 ∧ (run Q s detTape 4).halted = false ∧ (run Q s detTape 4).core.ptrs 53 = 0 ∧ (∀ x, x ≠ 53 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 4).core.regs 54 = ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ∧ (∀ x, x ≠ 54 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧ (run Q s detTape 4).core.mem = s.core.mem ∧ (run Q s detTape 4).integerMemory = s.integerMemory ∧ (run Q s detTape 4).work = s.work + 4 ∧ cellsWritten Q s 4 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b : ℝ) (s : State) (hpc : s.core.pc = off + 201) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = a) (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = b) (hb0 : ¬ (s.core.regs 52 - (b - a)) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 9).core.pc = off + 201 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 53 = s.core.ptrs 53 + 1 ∧ (run Q s detTape 9).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1 ∧ (∀ x, x ≠ 53 → x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs 44 = a ∧ (run Q s detTape 9).core.regs 45 = b ∧ (run Q s detTape 9).core.regs 47 = (b - a) ∧ (run Q s detTape 9).core.regs 54 = (s.core.regs 52 - (b - a)) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧ (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b : ℝ) (s : State) (hpc : s.core.pc = off + 201) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = a) (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = b) (hb0 : (s.core.regs 52 - (b - a)) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 210 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1 ∧ (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs 44 = a ∧ (run Q s detTape 7).core.regs 45 = b ∧ (run Q s detTape 7).core.regs 47 = (b - a) ∧ (run Q s detTape 7).core.regs 54 = (s.core.regs 52 - (b - a)) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 210) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 44),
      (run Q s detTape 16).core.pc = off + 258 ∧ (run Q s detTape 16).halted = false ∧ (run Q s detTape 16).core.ptrs 13 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 43 ∧ (run Q s detTape 16).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧ (run Q s detTape 16).core.ptrs 52 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 16).core.ptrs 57 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 16).core.ptrs 58 = 0 ∧ (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 16).core.regs 44 = ((s.core.regs 44 + s.core.regs 45) / s.core.regs 53) ∧ (∀ x, x ≠ 44 → (run Q s detTape 16).core.regs x = s.core.regs x) ∧ (run Q s detTape 16).core.mem = s.core.mem ∧ (run Q s detTape 16).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧ (run Q s detTape 16).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧ (run Q s detTape 16).integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧ (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 44 → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 16).work = s.work + 16 ∧ ∀ c ∈ cellsWritten Q s 16, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 44)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 226) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 17).core.pc = off + 258 ∧ (run Q s detTape 17).halted = false ∧ (run Q s detTape 17).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 17).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 17).core.ptrs 50 = s.core.ptrs 43 ∧ (run Q s detTape 17).core.ptrs 51 = s.core.ptrs 53 ∧ (run Q s detTape 17).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 17).core.ptrs 58 = 1 ∧ (run Q s detTape 17).core.ptrs 62 = s.core.ptrs 52 + 2 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 17).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 17).core.regs = s.core.regs ∧ (run Q s detTape 17).core.mem = s.core.mem ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 2 ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 17).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 17).work = s.work + 17 ∧ ∀ c ∈ cellsWritten Q s 17, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 243) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 15).core.pc = off + 34 ∧ (run Q s detTape 15).halted = false ∧ (run Q s detTape 15).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 15).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 15).core.ptrs 62 = s.core.ptrs 52 + 3 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → x ≠ 62 → (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 15).core.regs = s.core.regs ∧ (run Q s detTape 15).core.mem = s.core.mem ∧ (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧ (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 3 ∧ (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 15).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 15).work = s.work + 15 ∧ ∀ c ∈ cellsWritten Q s 15, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 258) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 261 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 14 = s.core.ptrs 14 - s.core.ptrs 60 ∧ (run Q s detTape 3).core.ptrs 46 = 0 ∧ (run Q s detTape 3).core.ptrs 56 = s.core.ptrs 14 - s.core.ptrs 60 ∧ (∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State) (hpc : s.core.pc = off + 261) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 50 + s.core.ptrs 46) = x) (hb0 : s.core.ptrs 46 < s.core.ptrs 60) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 261 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 56 + s.core.ptrs 46 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs 55 = x ∧ (∀ x, x ≠ 55 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem (s.core.ptrs 56 + s.core.ptrs 46) = x ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 46 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 56 + s.core.ptrs 46)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 261) (hh : s.halted = false) (hb0 : s.core.ptrs 60 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 268 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 58 ≤ s.core.ptrs 69) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 226 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 57 = s.core.ptrs 56 + s.core.ptrs 51 ∧ (∀ x, x ≠ 57 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 3).core.mem z = s.core.mem z) ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ ∀ c ∈ cellsWritten Q s 3, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : s.core.ptrs 58 ≤ 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 5).core.pc = off + 243 ∧ (run Q s detTape 5).halted = false ∧ (run Q s detTape 5).core.ptrs 57 = 1 ∧ (∀ x, x ≠ 57 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 5).core.regs = s.core.regs ∧ (run Q s detTape 5).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧ (run Q s detTape 5).integerMemory = s.integerMemory ∧ (run Q s detTape 5).work = s.work + 5 ∧ ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : 1 < s.core.ptrs 58) (hb2 : s.core.ptrs 58 ≤ 2) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 304 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 57 = 2 ∧ (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs = s.core.regs ∧ (run Q s detTape 7).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : 1 < s.core.ptrs 58) (hb2 : 2 < s.core.ptrs 58) (hb3 : s.core.ptrs 58 ≤ 3) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 9).core.pc = off + 321 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 57 = 3 ∧ (∀ x, x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : 1 < s.core.ptrs 58) (hb2 : 2 < s.core.ptrs 58) (hb3 : 3 < s.core.ptrs 58) (hb4 : s.core.ptrs 58 ≤ 4) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 11).core.pc = off + 348 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 57 = 4 ∧ (∀ x, x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 11).core.mem z = s.core.mem z) ∧ (run Q s detTape 11).integerMemory = s.integerMemory ∧ (run Q s detTape 11).work = s.work + 11 ∧ ∀ c ∈ cellsWritten Q s 11, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : 1 < s.core.ptrs 58) (hb2 : 2 < s.core.ptrs 58) (hb3 : 3 < s.core.ptrs 58) (hb4 : 4 < s.core.ptrs 58) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 12).core.pc = off + 366 ∧ (run Q s detTape 12).halted = false ∧ (run Q s detTape 12).core.ptrs 57 = 4 ∧ (∀ x, x ≠ 57 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 12).core.regs = s.core.regs ∧ (run Q s detTape 12).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 12).core.mem z = s.core.mem z) ∧ (run Q s detTape 12).integerMemory = s.integerMemory ∧ (run Q s detTape 12).work = s.work + 12 ∧ ∀ c ∈ cellsWritten Q s 12, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) :=
  ⟨tb_exit, tb_step, seg_sg0, sg_exit, sg_step, sgd_carve, sgd_split, la_next, la_found, seg_laf, seg_r0, seg_r1, cs_head, cl_step, cl_exit, cd_0, cd_1, cd_2, cd_3, cd_4, cd_5⟩

end DetANN.HPIM.BD.SB

namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem _root_.solution :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 134) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 161 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (mn lo mx hi : ℝ) (s : State) (hpc : s.core.pc = off + 134) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = mn) (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = lo) (fr2 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = mx) (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = hi) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 48 < s.core.ptrs 43),
      (run Q s detTape 27).core.pc = off + 134 ∧ (run Q s detTape 27).halted = false ∧ (run Q s detTape 27).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 27).core.ptrs 50 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (run Q s detTape 27).core.ptrs 57 = s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → (run Q s detTape 27).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 27).core.regs 44 = (mx + s.core.regs 49) ∧ (run Q s detTape 27).core.regs 45 = hi ∧ (run Q s detTape 27).core.regs 47 = ((((mx + s.core.regs 49) + hi) - Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi))) / s.core.regs 53) ∧ (run Q s detTape 27).core.regs 54 = Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi)) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 27).core.regs x = s.core.regs x) ∧ (run Q s detTape 27).core.mem (s.core.ptrs 48 + s.core.ptrs 46) = ((((mn - s.core.regs 49) + lo) + Real.sqrt (((mn - s.core.regs 49) - lo) * ((mn - s.core.regs 49) - lo))) / s.core.regs 53) ∧ (run Q s detTape 27).core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = ((((mx + s.core.regs 49) + hi) - Real.sqrt (((mx + s.core.regs 49) - hi) * ((mx + s.core.regs 49) - hi))) / s.core.regs 53) ∧ (∀ z, z ≠ s.core.ptrs 48 + s.core.ptrs 46 → z ≠ s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1 → (run Q s detTape 27).core.mem z = s.core.mem z) ∧ (run Q s detTape 27).integerMemory = s.integerMemory ∧ (run Q s detTape 27).work = s.work + 27 ∧ ∀ c ∈ cellsWritten Q s 27, c = (true, s.core.ptrs 48 + s.core.ptrs 46) ∨ c = (true, s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a0 b0 c0 d0 : ℝ) (s : State) (hpc : s.core.pc = off + 161) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48) = a0) (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 1) = b0) (fr2 : s.core.mem (s.core.ptrs 43) = c0) (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 1) = d0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 11).core.pc = off + 172 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 46 = 1 ∧ (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs 44 = c0 ∧ (run Q s detTape 11).core.regs 45 = d0 ∧ (run Q s detTape 11).core.regs 51 = (b0 - a0) ∧ (run Q s detTape 11).core.regs 52 = (d0 - c0) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 51 → x ≠ 52 → (run Q s detTape 11).core.regs x = s.core.regs x) ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).integerMemory = s.integerMemory ∧ (run Q s detTape 11).work = s.work + 11 ∧ cellsWritten Q s 11 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 172) (hh : s.halted = false) (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 197 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b c d : ℝ) (s : State) (hpc : s.core.pc = off + 172) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46) = a) (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 46 + s.core.ptrs 1) = b) (fr2 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46) = c) (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1) = d) (hb0 : s.core.ptrs 46 < s.core.ptrs 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 25).core.pc = off + 172 ∧ (run Q s detTape 25).halted = false ∧ (run Q s detTape 25).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 25).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 46 + s.core.ptrs 1 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 25).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 25).core.regs 44 = c ∧ (run Q s detTape 25).core.regs 45 = d ∧ (run Q s detTape 25).core.regs 47 = (d - c) ∧ (run Q s detTape 25).core.regs 51 = (((s.core.regs 51 + (b - a)) + Real.sqrt ((s.core.regs 51 - (b - a)) * (s.core.regs 51 - (b - a)))) / s.core.regs 53) ∧ (run Q s detTape 25).core.regs 52 = (((s.core.regs 52 + (d - c)) + Real.sqrt ((s.core.regs 52 - (d - c)) * (s.core.regs 52 - (d - c)))) / s.core.regs 53) ∧ (run Q s detTape 25).core.regs 54 = Real.sqrt ((s.core.regs 52 - (d - c)) * (s.core.regs 52 - (d - c))) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 51 → x ≠ 52 → x ≠ 54 → (run Q s detTape 25).core.regs x = s.core.regs x) ∧ (run Q s detTape 25).core.mem = s.core.mem ∧ (run Q s detTape 25).integerMemory = s.integerMemory ∧ (run Q s detTape 25).work = s.work + 25 ∧ cellsWritten Q s 25 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hb0 : ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 280 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs = s.core.ptrs ∧ (run Q s detTape 3).core.regs 54 = ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ∧ (∀ x, x ≠ 54 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hb0 : ¬ ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 4).core.pc = off + 201 ∧ (run Q s detTape 4).halted = false ∧ (run Q s detTape 4).core.ptrs 53 = 0 ∧ (∀ x, x ≠ 53 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 4).core.regs 54 = ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ∧ (∀ x, x ≠ 54 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧ (run Q s detTape 4).core.mem = s.core.mem ∧ (run Q s detTape 4).integerMemory = s.integerMemory ∧ (run Q s detTape 4).work = s.work + 4 ∧ cellsWritten Q s 4 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b : ℝ) (s : State) (hpc : s.core.pc = off + 201) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = a) (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = b) (hb0 : ¬ (s.core.regs 52 - (b - a)) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 9).core.pc = off + 201 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 53 = s.core.ptrs 53 + 1 ∧ (run Q s detTape 9).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1 ∧ (∀ x, x ≠ 53 → x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs 44 = a ∧ (run Q s detTape 9).core.regs 45 = b ∧ (run Q s detTape 9).core.regs 47 = (b - a) ∧ (run Q s detTape 9).core.regs 54 = (s.core.regs 52 - (b - a)) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 9).core.regs x = s.core.regs x) ∧ (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a b : ℝ) (s : State) (hpc : s.core.pc = off + 201) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53) = a) (fr1 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1) = b) (hb0 : (s.core.regs 52 - (b - a)) ≤ 0) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 210 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 53 + s.core.ptrs 1 ∧ (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs 44 = a ∧ (run Q s detTape 7).core.regs 45 = b ∧ (run Q s detTape 7).core.regs 47 = (b - a) ∧ (run Q s detTape 7).core.regs 54 = (s.core.regs 52 - (b - a)) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 210) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1) (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 44),
      (run Q s detTape 16).core.pc = off + 258 ∧ (run Q s detTape 16).halted = false ∧ (run Q s detTape 16).core.ptrs 13 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 43 ∧ (run Q s detTape 16).core.ptrs 51 = s.core.ptrs 1 + s.core.ptrs 53 ∧ (run Q s detTape 16).core.ptrs 52 = s.core.ptrs 13 - 4 ∧ (run Q s detTape 16).core.ptrs 57 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 16).core.ptrs 58 = 0 ∧ (∀ x, x ≠ 13 → x ≠ 50 → x ≠ 51 → x ≠ 52 → x ≠ 57 → x ≠ 58 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 16).core.regs 44 = ((s.core.regs 44 + s.core.regs 45) / s.core.regs 53) ∧ (∀ x, x ≠ 44 → (run Q s detTape 16).core.regs x = s.core.regs x) ∧ (run Q s detTape 16).core.mem = s.core.mem ∧ (run Q s detTape 16).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 68 ∧ (run Q s detTape 16).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧ (run Q s detTape 16).integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧ (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 44 → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 16).work = s.work + 16 ∧ ∀ c ∈ cellsWritten Q s 16, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 44)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 226) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 17).core.pc = off + 258 ∧ (run Q s detTape 17).halted = false ∧ (run Q s detTape 17).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 17).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 17).core.ptrs 50 = s.core.ptrs 43 ∧ (run Q s detTape 17).core.ptrs 51 = s.core.ptrs 53 ∧ (run Q s detTape 17).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 17).core.ptrs 58 = 1 ∧ (run Q s detTape 17).core.ptrs 62 = s.core.ptrs 52 + 2 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 50 → x ≠ 51 → x ≠ 57 → x ≠ 58 → x ≠ 62 → (run Q s detTape 17).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 17).core.regs = s.core.regs ∧ (run Q s detTape 17).core.mem = s.core.mem ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 2 ∧ (run Q s detTape 17).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 17).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 17).work = s.work + 17 ∧ ∀ c ∈ cellsWritten Q s 17, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 243) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 15).core.pc = off + 34 ∧ (run Q s detTape 15).halted = false ∧ (run Q s detTape 15).core.ptrs 13 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 13 - 3 ∧ (run Q s detTape 15).core.ptrs 57 = s.core.ptrs 13 - 1 ∧ (run Q s detTape 15).core.ptrs 62 = s.core.ptrs 52 + 3 ∧ (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → x ≠ 62 → (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 15).core.regs = s.core.regs ∧ (run Q s detTape 15).core.mem = s.core.mem ∧ (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 56 ∧ (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 52 + 3 ∧ (run Q s detTape 15).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧ (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 15).integerMemory z = s.integerMemory z) ∧ (run Q s detTape 15).work = s.work + 15 ∧ ∀ c ∈ cellsWritten Q s 15, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 258) (hh : s.halted = false) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 261 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 14 = s.core.ptrs 14 - s.core.ptrs 60 ∧ (run Q s detTape 3).core.ptrs 46 = 0 ∧ (run Q s detTape 3).core.ptrs 56 = s.core.ptrs 14 - s.core.ptrs 60 ∧ (∀ x, x ≠ 14 → x ≠ 46 → x ≠ 56 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem = s.core.mem ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ cellsWritten Q s 3 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (x : ℝ) (s : State) (hpc : s.core.pc = off + 261) (hh : s.halted = false) (fr0 : s.core.mem (s.core.ptrs 50 + s.core.ptrs 46) = x) (hb0 : s.core.ptrs 46 < s.core.ptrs 60) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 261 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 46 = s.core.ptrs 46 + 1 ∧ (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 56 + s.core.ptrs 46 ∧ (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs 55 = x ∧ (∀ x, x ≠ 55 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem (s.core.ptrs 56 + s.core.ptrs 46) = x ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 46 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 56 + s.core.ptrs 46)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 261) (hh : s.halted = false) (hb0 : s.core.ptrs 60 ≤ s.core.ptrs 46) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 1).core.pc = off + 268 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs = s.core.ptrs ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 58 ≤ s.core.ptrs 69) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 3).core.pc = off + 226 ∧ (run Q s detTape 3).halted = false ∧ (run Q s detTape 3).core.ptrs 57 = s.core.ptrs 56 + s.core.ptrs 51 ∧ (∀ x, x ≠ 57 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 3).core.regs = s.core.regs ∧ (run Q s detTape 3).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 3).core.mem z = s.core.mem z) ∧ (run Q s detTape 3).integerMemory = s.integerMemory ∧ (run Q s detTape 3).work = s.work + 3 ∧ ∀ c ∈ cellsWritten Q s 3, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : s.core.ptrs 58 ≤ 1) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 5).core.pc = off + 243 ∧ (run Q s detTape 5).halted = false ∧ (run Q s detTape 5).core.ptrs 57 = 1 ∧ (∀ x, x ≠ 57 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 5).core.regs = s.core.regs ∧ (run Q s detTape 5).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧ (run Q s detTape 5).integerMemory = s.integerMemory ∧ (run Q s detTape 5).work = s.work + 5 ∧ ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : 1 < s.core.ptrs 58) (hb2 : s.core.ptrs 58 ≤ 2) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 7).core.pc = off + 304 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 57 = 2 ∧ (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs = s.core.regs ∧ (run Q s detTape 7).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 7).core.mem z = s.core.mem z) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : 1 < s.core.ptrs 58) (hb2 : 2 < s.core.ptrs 58) (hb3 : s.core.ptrs 58 ≤ 3) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 9).core.pc = off + 321 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 57 = 3 ∧ (∀ x, x ≠ 57 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 9).core.mem z = s.core.mem z) ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ ∀ c ∈ cellsWritten Q s 9, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : 1 < s.core.ptrs 58) (hb2 : 2 < s.core.ptrs 58) (hb3 : 3 < s.core.ptrs 58) (hb4 : s.core.ptrs 58 ≤ 4) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 11).core.pc = off + 348 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 57 = 4 ∧ (∀ x, x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 11).core.mem z = s.core.mem z) ∧ (run Q s detTape 11).integerMemory = s.integerMemory ∧ (run Q s detTape 11).work = s.work + 11 ∧ ∀ c ∈ cellsWritten Q s 11, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State) (hpc : s.core.pc = off + 268) (hh : s.halted = false) (hb0 : s.core.ptrs 69 < s.core.ptrs 58) (hb1 : 1 < s.core.ptrs 58) (hb2 : 2 < s.core.ptrs 58) (hb3 : 3 < s.core.ptrs 58) (hb4 : 4 < s.core.ptrs 58) (hm1 : 1 ≤ s.core.ptrs 1),
      (run Q s detTape 12).core.pc = off + 366 ∧ (run Q s detTape 12).halted = false ∧ (run Q s detTape 12).core.ptrs 57 = 4 ∧ (∀ x, x ≠ 57 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 12).core.regs = s.core.regs ∧ (run Q s detTape 12).core.mem (s.core.ptrs 56 + s.core.ptrs 51) = s.core.regs 44 ∧ (∀ z, z ≠ s.core.ptrs 56 + s.core.ptrs 51 → (run Q s detTape 12).core.mem z = s.core.mem z) ∧ (run Q s detTape 12).integerMemory = s.integerMemory ∧ (run Q s detTape 12).work = s.work + 12 ∧ ∀ c ∈ cellsWritten Q s 12, c = (true, s.core.ptrs 56 + s.core.ptrs 51)) :=
  DetANN.HPIM.BD.SB.split_steps'

end DetANN.HPIM.BD

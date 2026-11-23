-- Prove2me | solution 1 for DetANN.reloc_sim_timed_cells
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:13:44.256589+00:00
-- url     : https://prove2.me/submissions/9f3aa278-ed3d-4cd7-a30d-52b6c094a139

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Definitions.Def_DetANN_DataStructure
import Theorems.Thm_DetANN_reloc_sim_cells
import Theorems.Thm_PNormReg_run_work_eq

open PNormReg PNormRegLib DetANN

namespace DetANNTimedCellsAux

lemma run_succ (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    run P s ω (t + 1) = run P (step P ω s) ω t := by
  simp only [run, Function.iterate_succ_apply]

lemma step_work_le (P : Program) (ω : ℕ → Bool) (s : State) :
    (step P ω s).work ≤ s.work + 1 := by
  by_cases h : s.halted = true
  · simp [step, h]
  · have h' : s.halted = false := Bool.eq_false_of_not_eq_true h
    rw [step, if_neg (by simp [h'])]
    split <;> simp

lemma run_work_le (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    (run P s ω t).work ≤ s.work + t := by
  induction t generalizing s with
  | zero => simp [run]
  | succ t ih =>
    rw [run_succ]
    have h := ih (step P ω s)
    have h' := step_work_le P ω s
    omega

end DetANNTimedCellsAux

open DetANNTimedCellsAux in
theorem solution (p : RelocParams) (F : Frame) (P Q : Program) (X : ℤ)
    (hE : Embeds Q (reloc p P) p.cOff) (hV : Valid p F) (hU : UsesBelow P F.nR F.nQ)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) (Y : ℤ) (r v : State) (hS : Sim p F r v)
    (hB : PBounded Y v) (hXY : X ≤ Y) (hR : Y * 2 ^ t ≤ F.R)
    (hh : (run P v detTape t).halted = true) :
    ∃ t', Agree p F (run Q r detTape t') (run P v detTape t) ∧
      (run Q r detTape t').core.pc = p.exit ∧ (run Q r detTape t').halted = false ∧
      cellsWritten Q r t' = (cellsWritten P v t).image (fun c => (c.1, F.b + c.2)) ∧
      (run Q r detTape t').work = r.work + t' ∧ t' ≤ 2 * t := by
  obtain ⟨t', hA, hpc, hr, hc⟩ :=
    reloc_sim_cells p F P Q X hE hV hU hlit hX t Y r v hS hB hXY hR hh
  have hw : (run Q r detTape t').work = r.work + t' :=
    run_work_eq Q r detTape t' hS.2.1 hr
  refine ⟨t', hA, hpc, hr, hc, hw, ?_⟩
  have hstart : r.work = F.c + 2 * v.work := hS.1.2.2.2.2.2.2.2.2
  have hend : (run Q r detTape t').work = F.c + 2 * (run P v detTape t).work :=
    hA.2.2.2.2.2.2.2.2
  have hvirt := run_work_le P v detTape t
  omega

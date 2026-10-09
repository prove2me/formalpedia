-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.criticallyDamped_energy_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:47:26.344587+00:00
-- url     : https://prove2.me/submissions/41221fc8-5565-4148-8f77-798553557d84

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.criticallyDamped_energy_strictAnti
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
import Theorems.Thm_BookProof_DampedOscillatorEnergy_criticallyDamped_energy
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution :
    StrictAnti (dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s))) := by

  intro s t hst
  rw [criticallyDamped_energy, criticallyDamped_energy]
  have h : Real.exp (-t) < Real.exp (-s) := Real.exp_lt_exp.mpr (by linarith)
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  nlinarith [Real.exp_pos (-s)]

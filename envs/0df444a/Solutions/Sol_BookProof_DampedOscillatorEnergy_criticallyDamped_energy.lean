-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.criticallyDamped_energy
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:47:13.52853+00:00
-- url     : https://prove2.me/submissions/6b1401f8-6840-4614-a993-3c1eb75d8e71

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.criticallyDamped_energy
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s)) t
      = Real.exp (-t) ^ 2 := by

  simp [dampedEnergy]

-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_vel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:46:45.446727+00:00
-- url     : https://prove2.me/submissions/887c5cd2-1f5e-425e-a5a1-5c4955c3432e

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_vel
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
import Theorems.Thm_BookProof_DampedOscillatorEnergy_criticallyDamped_hasDerivAt_pos
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    HasDerivAt (fun s => -Real.exp (-s)) (Real.exp (-t)) t := by

  have h := (criticallyDamped_hasDerivAt_pos t).neg
  simp at h
  exact h

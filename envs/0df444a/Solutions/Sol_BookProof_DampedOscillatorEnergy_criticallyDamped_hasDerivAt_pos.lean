-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:46:44.52783+00:00
-- url     : https://prove2.me/submissions/d57922ee-0885-4019-9a39-1f0d454df920

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_pos
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by

  have h := (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
  simp at h
  exact h

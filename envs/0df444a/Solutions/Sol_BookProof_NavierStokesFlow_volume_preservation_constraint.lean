-- Prove2me | solution 1 for BookProof.NavierStokesFlow.volume_preservation_constraint
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:15:03.500302+00:00
-- url     : https://prove2.me/submissions/68bf5510-a71c-4477-be28-538a083910a8

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- Direct proof from the registered statement using Mathlib.
theorem solution {d : ℕ} (f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hdet : LinearMap.det f = 1) (s : Set (Fin d → ℝ)) :
    MeasureTheory.volume (f '' s) = MeasureTheory.volume s := by
  simpa [hdet] using MeasureTheory.Measure.addHaar_image_linearMap
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) f s

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution

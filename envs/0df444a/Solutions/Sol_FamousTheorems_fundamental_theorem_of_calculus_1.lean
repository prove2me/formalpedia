-- Prove2me | solution 1 for FamousTheorems.fundamental_theorem_of_calculus_1
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:48:45.920579+00:00
-- url     : https://prove2.me/submissions/62093c5d-31b9-4e51-aa62-293463338cb2

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) (hmeas : StronglyMeasurableAtFilter f (nhds b) MeasureTheory.volume)
    (hb : ContinuousAt f b) : HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b := by
  exact intervalIntegral.integral_hasDerivAt_right hf hmeas hb

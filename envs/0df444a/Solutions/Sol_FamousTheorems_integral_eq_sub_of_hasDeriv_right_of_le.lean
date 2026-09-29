-- Prove2me | solution 1 for FamousTheorems.integral_eq_sub_of_hasDeriv_right_of_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:45:36.836628+00:00
-- url     : https://prove2.me/submissions/78bd73da-6aa8-4f92-8dab-efbc99fa4cc9

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Real Topology ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f f' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f (f' x) (Set.Ioi x) x)
    (f'int : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv f'int

-- Prove2me | solution 1 for AvramDividend.Classical.chat07_integrableOn_positive_halfline_of_uniform_interval_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:40:36.00679+00:00
-- url     : https://prove2.me/submissions/6f40a428-7624-420f-8247-4c5c63c6b0f3

import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

/-! Uniform bounds on finite-interval absolute integrals imply integrability
on the positive half-line by the pinned improper-integral criterion. -/
theorem solution
    (f : ℝ → ℝ) (I : ℝ)
    (hlocal : ∀ n : ℕ,
      IntervalIntegrable f volume 0 (n : ℝ))
    (hbounded : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..(n : ℝ), |f x|) ≤ I) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  refine MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (l := Filter.atTop) (b := fun n : ℕ => (n : ℝ)) I 0 ?_ ?_ ?_
  · intro n
    exact (hlocal n).1
  · exact tendsto_natCast_atTop_atTop
  · exact Filter.Eventually.of_forall (by
      intro n
      simpa only [Real.norm_eq_abs] using hbounded n)

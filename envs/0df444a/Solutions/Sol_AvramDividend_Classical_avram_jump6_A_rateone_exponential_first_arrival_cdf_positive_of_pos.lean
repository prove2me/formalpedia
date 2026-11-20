-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_rateone_exponential_first_arrival_cdf_positive_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:32:31.51817+00:00
-- url     : https://prove2.me/submissions/de6c3398-10e5-4551-ba27-37b7367f6fae

import Mathlib.Probability.Distributions.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
noncomputable section
theorem solution
    (t : ℝ) (ht : 0 < t) :
    0 < cdf (expMeasure (1 : ℝ)) t := by
  have heq := cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1) t
  simp only [le_of_lt ht, if_true] at heq
  have hx : -(1 * t) < (0 : ℝ) := by nlinarith
  have hExp : Real.exp (-(1 * t)) < 1 :=
    Real.exp_lt_one_iff.mpr hx
  have hReal : (0 : ℝ) < 1 - Real.exp (-(1 * t)) := by
    linarith
  have hc : cdf (expMeasure (1 : ℝ)) (t) =
      1 - Real.exp (-(t)) := by
    simpa only [one_mul] using heq
  rw [hc]
  simpa only [one_mul] using hReal

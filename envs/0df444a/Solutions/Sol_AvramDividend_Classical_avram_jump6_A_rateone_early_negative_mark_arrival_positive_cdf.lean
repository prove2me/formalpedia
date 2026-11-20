-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_rateone_early_negative_mark_arrival_positive_cdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:26:37.971395+00:00
-- url     : https://prove2.me/submissions/56c9a592-b91a-483d-aa30-192a5208ada0

import Mathlib.Probability.Distributions.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open ProbabilityTheory MeasureTheory
noncomputable section
theorem solution :
    0 < (cdf (expMeasure (1 : ℝ))) (1 / 10 : ℝ) := by
  have heq := cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1)
    (1 / 10 : ℝ)
  simp only [show (0 : ℝ) ≤ 1 / 10 by norm_num, if_true] at heq
  have he : Real.exp (-(1 / 10 : ℝ)) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hp : (0 : ℝ) < 1 - Real.exp (-(1 / 10 : ℝ)) := by
    linarith
  have hc : cdf (expMeasure (1 : ℝ)) (1 / 10 : ℝ) =
      1 - Real.exp (-(1 / 10 : ℝ)) := by
    simpa only [one_mul] using heq
  rw [hc]
  exact hp

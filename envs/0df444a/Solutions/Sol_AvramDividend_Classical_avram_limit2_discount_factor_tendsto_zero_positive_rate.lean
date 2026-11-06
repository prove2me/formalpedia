-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_discount_factor_tendsto_zero_positive_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:17:06.973754+00:00
-- url     : https://prove2.me/submissions/004fcfbd-9ca5-46a6-8184-065dfc986e40

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped ENNReal

/-! CE repair two: unfold composition and commute the scalar factor. -/
theorem solution
    (q : ℝ) (hq : 0 < q) :
    Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hreal : Tendsto (fun n : ℕ => Real.exp (-(q * (n : ℝ))))
      atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hnat.atTop_mul_const hq))
  simpa using (ENNReal.tendsto_ofReal hreal)

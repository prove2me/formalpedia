-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_discount_factor_ennreal_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:37:50.617694+00:00
-- url     : https://prove2.me/submissions/81be2e71-c99f-48d3-9381-a82e321dbd6f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-- The original nonnegative-time dividend discount factor is at most one
    when q is nonnegative, in the ENNReal integral's exact form. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) ≤ 1 := by
  have hqt : 0 ≤ q * (t : ℝ) := mul_nonneg hq t.property
  have hexp : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hexp

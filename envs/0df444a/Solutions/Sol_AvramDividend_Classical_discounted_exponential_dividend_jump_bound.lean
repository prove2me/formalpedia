-- Prove2me | solution 1 for AvramDividend.Classical.discounted_exponential_dividend_jump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:41:15.354478+00:00
-- url     : https://prove2.me/submissions/9f673040-8859-4408-a87b-b340b4abcf64

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exponential_dividend_jump_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (θ q u d : ℝ) (t : ℝ≥0)
    (hθ : 1 ≤ θ) (hd : 0 ≤ d) (hcap : d ≤ u) :
    Real.exp (-(q * (t : ℝ))) * d ≤
      Real.exp (-(q * (t : ℝ))) *
      (Real.exp (θ * u) - Real.exp (θ * (u - d))) := by
  exact mul_le_mul_of_nonneg_left
    (exponential_dividend_jump_bound θ u d hθ hd hcap)
    (Real.exp_pos _).le

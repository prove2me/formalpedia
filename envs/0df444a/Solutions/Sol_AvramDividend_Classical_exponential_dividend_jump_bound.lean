-- Prove2me | solution 1 for AvramDividend.Classical.exponential_dividend_jump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:21:54.166848+00:00
-- url     : https://prove2.me/submissions/1576b783-3f64-4917-aa11-4e3482b997af

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exponential_dividend_lump_sum_gap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (θ x d : ℝ) (hθ : 1 ≤ θ) (hd : 0 ≤ d) (hcap : d ≤ x) :
    d ≤ Real.exp (θ * x) - Real.exp (θ * (x - d)) := by
  have hu : 0 ≤ x - d := sub_nonneg.mpr hcap
  simpa only [sub_add_cancel] using
    (exponential_dividend_lump_sum_gap θ (x - d) d hθ hu hd)

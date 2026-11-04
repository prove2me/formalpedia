-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_discount_of_nonnegative_time_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:41:09.275747+00:00
-- url     : https://prove2.me/submissions/ce0213d5-07d1-434a-9f3d-0be6370ebba7

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Discounted original Cash payment selectors are subunit for q≥0,s≥0. -/
theorem solution
    (ρ : ℝ≥0∞) (q s : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    (if s ∈ paymentTimes ρ then
        ENNReal.ofReal (Real.exp (-(q * s))) else 0) ≤ 1 := by
  by_cases htime : s ∈ paymentTimes ρ
  · simp only [if_pos htime]
    have hreal : Real.exp (-(q * s)) ≤ (1 : ℝ) := by
      exact Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hq hs))
    simpa using (ENNReal.ofReal_le_ofReal hreal)
  · simp [htime]

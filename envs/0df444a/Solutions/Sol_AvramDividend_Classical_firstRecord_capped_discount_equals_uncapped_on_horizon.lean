-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_discount_equals_uncapped_on_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:18:35.553978+00:00
-- url     : https://prove2.me/submissions/86d1bb62-806a-4fe5-9e62-e7ee3dd6afbf

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Before a finite horizon the capped record carries exactly the uncapped discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε q : ℝ) (N : ℝ≥0) (ω : Ω)
    (hN : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    ENNReal.ofReal ε *
      ENNReal.ofReal (Real.exp (-(q *
        (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ)))) =
    ENNReal.ofReal ε *
      ENNReal.ofReal (Real.exp (-(q *
        (twoSidedExitUpTime X b ω).toReal))) := by
  have hclock := firstRecord_capped_clock_eq_uncapped_of_le_horizon
    X b N ω hN
  have hreal :
      (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ) =
      (twoSidedExitUpTime X b ω).toReal := by
    simpa only [ENNReal.toReal, ENNReal.toNNReal_coe] using
      congrArg ENNReal.toReal hclock
  rw [hreal]

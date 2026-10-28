-- Prove2me | solution 1 for AvramDividend.Classical.barrier_strategy_value_zero_all_capital_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:46:32.540316+00:00
-- url     : https://prove2.me/submissions/e96c6fc3-3f45-49a7-a8c4-d6d9f7b700b9

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every zero-barrier initial surplus follows from the boundary valuation and initial-excess payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hboundary : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0))
    (hval : 0 ≤ barrierValue W 0 0)
    (x : ℝ) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal (barrierValue W 0 x) := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · rw [← hzero]
    exact hboundary
  · exact barrierStrategy_above_value_of_boundary
      X q W 0 x (le_refl 0) hpos hboundary hval

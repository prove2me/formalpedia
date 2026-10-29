-- Prove2me | solution 3 for AvramDividend.Classical.barrier_strategy_value_zero_all_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:07:59.034404+00:00
-- url     : https://prove2.me/submissions/94205870-576d-4e52-bb05-1781192c8e0a

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital_of_boundary
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- All-reserve zero-barrier valuation follows from its single boundary identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal (barrierValue W 0 x) := by
  obtain ⟨hval, hboundary⟩ :=
    barrier_zero_boundary_value_nonneg X hX q hq W hW
  exact barrier_strategy_value_zero_all_capital_of_boundary
    X q W hboundary hval x hx

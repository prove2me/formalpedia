-- Prove2me | solution 4 for AvramDividend.Classical.barrier_strategy_value_zero_all_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:16:39.529121+00:00
-- url     : https://prove2.me/submissions/029419bf-7a05-4337-a23b-0f9f8f86068e

import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_zero_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Zero-level barrier values are affine in the initial capital once the boundary value is known. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal (barrierValue W 0 x) := by
  exact barrier_strategy_value_zero_all_capital_of_boundary X q W
    (barrierStrategy_zero_boundary_value_identity X hX q hq W hW)
    (barrierValue_zero_zero_nonneg X hX q hq W hW) x hx

-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound_all_of_boundary_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:20:58.577759+00:00
-- url     : https://prove2.me/submissions/26d64ba3-2806-402a-8c28-f852b57f6563

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_zero_nonneg
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact zero-barrier boundary identity alone yields the capped optimal
dividend-value upper bound at every nonnegative reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hboundary : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  have hval : 0 ≤ barrierValue W 0 0 :=
    barrierValue_zero_zero_nonneg X hX q hq W hW
  have hzero : valueFunctionLe X q 0 0 ≤
      ENNReal.ofReal (barrierValue W 0 0) :=
    zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W hboundary
  intro x hx
  exact zero_cap_value_upper_bound_of_zero_bound X q W hzero hval x hx

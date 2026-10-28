-- Prove2me | solution 5 for AvramDividend.Classical.zero_cap_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:11:31.098349+00:00
-- url     : https://prove2.me/submissions/e58462cf-34ea-4020-add1-6c5cd3f2f4f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_zero_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The zero-cap bound at all reserves follows from the boundary value
through proved stochastic and affine transfer theorems. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  intro x hx
  have hboundary :
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) :=
    barrier_zero_boundary_value X hX q hq W hW
  have hzero :
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) :=
    zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W hboundary
  exact zero_cap_value_upper_bound_of_zero_bound
    X q W hzero (barrierValue_zero_zero_nonneg X hX q hq W hW) x hx

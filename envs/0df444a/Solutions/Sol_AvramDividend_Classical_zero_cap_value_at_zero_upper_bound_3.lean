-- Prove2me | solution 3 for AvramDividend.Classical.zero_cap_value_at_zero_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:00:49.087645+00:00
-- url     : https://prove2.me/submissions/a395f656-8907-480a-9a92-5f416ac00e86

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg
import Theorems.Thm_AvramDividend_Classical_local_verification_per_strategy_to_capped_value_bound
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original zero-cap verification bound reduces to the zero-barrier endpoint valuation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  apply local_verification_per_strategy_to_capped_value_bound
    X q 0 0 (barrierValue W 0)
  intro D hD
  calc
    dividendValue X q 0 D ≤
        dividendValue X q 0 (barrierStrategy X 0 0) :=
      zero_cap_admissible_dividendValue_le_barrier_at_zero X hX q hq D hD
    _ = ENNReal.ofReal (barrierValue W 0 0) :=
      (barrier_zero_boundary_value_nonneg X hX q hq W hW).2

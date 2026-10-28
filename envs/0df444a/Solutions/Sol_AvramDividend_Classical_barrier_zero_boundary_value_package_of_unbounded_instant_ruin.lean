-- Prove2me | solution 1 for AvramDividend.Classical.barrier_zero_boundary_value_package_of_unbounded_instant_ruin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:01:23.330598+00:00
-- url     : https://prove2.me/submissions/57e9c212-2f0b-4965-8666-07527bcdd46b

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  refine ⟨?_, ?_⟩
  · rw [barrierValue_zero_of_scale_zero W
      (chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW)]
  · rw [barrierValue_self_eq_barrierSupValue X q 0]
    exact zero_reflectedSupValue_of_unbounded_instant_ruin X q hq W hW hnbv hRuin
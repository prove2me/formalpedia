-- Prove2me | solution 6 for AvramDividend.Classical.barrier_zero_boundary_value_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:55:10.628491+00:00
-- url     : https://prove2.me/submissions/547e3d84-02da-4bd1-a309-ea8ce3af7217

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Reuse the canonical zero-barrier identity in the joint boundary package. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  exact ⟨barrierValue_zero_boundary_nonneg X hX q hq W hW,
    barrierStrategy_zero_boundary_value_identity X hX q hq W hW⟩

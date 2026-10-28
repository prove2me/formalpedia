-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_zero_discount_C1_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:47:08.029788+00:00
-- url     : https://prove2.me/submissions/55d94a6a-d89b-4458-bb03-1037ae064ba9

import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_gaussian_of_positive_scale_exists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Close the Gaussian zero-discount C1 branch using the proved positive-q scale construction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hnbv : ¬ X.BoundedVariation) (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) := by
  have hq : (0 : ℝ) < 1 := zero_lt_one
  obtain ⟨Wq, hWq⟩ :=
    unbounded_positive_discount_scale_exists_from_zero
      X hnbv W₀ hW₀ 1 hq
  exact unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
    X hnbv W₀ hW₀ hσ ⟨1, hq, Wq, hWq⟩

-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_zero_origin_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:55:57.706376+00:00
-- url     : https://prove2.me/submissions/5c6292e4-2e81-48e4-bc4f-2db5d197204a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_psi_normalised_unbounded_small_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Zero-discount unbounded-variation scale functions start at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (hW : IsScaleFunction X 0 W)
    (hnbv : ¬ X.BoundedVariation) :
    W 0 = 0 := by
  by_cases hσ : 0 < X.σ
  · have hgrowth := gaussian_psi_superlinear_of_positive_sigma X hσ
    exact scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
      X 0 (le_refl _) W hW hgrowth
  · have hσzero : X.σ = 0 :=
      le_antisymm (le_of_not_gt hσ) X.σ_nonneg
    have hinf : (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
      by_contra hnot
      apply hnbv
      exact ⟨hσzero, lt_top_iff_ne_top.mpr hnot⟩
    have hgrowth := psi_normalised_unbounded_small_jumps X hσzero hinf
    exact scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
      X 0 (le_refl _) W hW hgrowth

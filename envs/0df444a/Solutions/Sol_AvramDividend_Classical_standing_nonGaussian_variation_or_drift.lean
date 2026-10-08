-- Prove2me | solution 1 for AvramDividend.Classical.standing_nonGaussian_variation_or_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:55:05.90841+00:00
-- url     : https://prove2.me/submissions/eb6cc38b-5512-48ee-89d6-3bd2d9fee4bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hσ : X.σ = 0) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ ∨
      0 < X.drift := by
  by_cases hfinite :
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤
  · right
    have hBV : X.BoundedVariation := ⟨hσ, hfinite⟩
    by_contra hnot
    have hle : X.drift ≤ 0 := le_of_not_gt hnot
    exact hX.1 ⟨hBV, Or.inl hle⟩
  · left
    exact le_antisymm le_top (le_of_not_gt hfinite)

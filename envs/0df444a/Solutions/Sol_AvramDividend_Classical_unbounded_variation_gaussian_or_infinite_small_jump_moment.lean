-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_gaussian_or_infinite_small_jump_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:14:46.730761+00:00
-- url     : https://prove2.me/submissions/f464d7d5-f2e4-42fd-86d9-e36d1086690d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- An unbounded-variation spectrally negative Lévy process must have
positive Gaussian variance coefficient or infinite small-jump first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    0 < X.σ ∨
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
  by_cases hσ : X.σ = 0
  · right
    by_contra hfinite
    apply hnbv
    exact ⟨hσ, lt_top_iff_ne_top.mpr hfinite⟩
  · left
    exact lt_of_le_of_ne X.σ_nonneg (Ne.symm hσ)

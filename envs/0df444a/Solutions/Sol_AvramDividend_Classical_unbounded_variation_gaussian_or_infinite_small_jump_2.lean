-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_variation_gaussian_or_infinite_small_jump
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:17:31.606886+00:00
-- url     : https://prove2.me/submissions/bb082f3a-1c75-487c-940e-ca57e247635f

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    0 < X.σ ∨
      (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) = ⊤ := by 
  unfold SpectrallyNegativeLevy.BoundedVariation at hnbv
  by_cases hσ : X.σ = 0
  · right
    by_contra h
    exact hnbv ⟨hσ, lt_top_iff_ne_top.2 h⟩
  · left
    exact lt_of_le_of_ne X.σ_nonneg (Ne.symm hσ)

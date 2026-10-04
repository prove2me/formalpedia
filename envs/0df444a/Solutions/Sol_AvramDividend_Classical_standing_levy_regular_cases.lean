-- Prove2me | solution 1 for AvramDividend.Classical.standing_levy_regular_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T18:43:45.771382+00:00
-- url     : https://prove2.me/submissions/5afa6e56-3f81-48d1-a4f5-2e909b126ac8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) :
    (X.BoundedVariation ∧ 0 < X.drift ∧ X.ν ≪ (volume : Measure ℝ)) ∨
      (0 < X.σ ∨
        (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) := by
  classical
  by_cases hbv : X.BoundedVariation
  · left
    have hδ : 0 < X.drift := by
      by_contra h
      exact hX.1 ⟨hbv, Or.inl (le_of_not_gt h)⟩
    have hac : X.ν ≪ (volume : Measure ℝ) := by
      rcases hX.2.2 with hσ | hinfty | hac
      · have hσzero : X.σ = 0 := hbv.1
        rw [hσzero] at hσ
        exact False.elim (lt_irrefl (0 : ℝ) hσ)
      · exact False.elim ((ne_of_lt hbv.2) hinfty)
      · exact hac
    exact ⟨hbv, hδ, hac⟩
  · right
    rcases lt_or_eq_of_le X.σ_nonneg with hσ | hσ
    · exact Or.inl hσ
    · right
      apply le_antisymm le_top
      apply le_of_not_gt
      intro hfinite
      exact hbv ⟨hσ.symm, hfinite⟩

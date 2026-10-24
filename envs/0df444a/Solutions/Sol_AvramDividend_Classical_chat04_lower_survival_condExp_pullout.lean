-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_survival_condExp_pullout
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:56:43.848137+00:00
-- url     : https://prove2.me/submissions/4c2f3764-5bcc-4cf0-bddd-0babc42f24c0

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The historical one-sided ruin-survival indicator is measurable at
observation time T and pulls through conditional expectation. Future
path-dependent rewards remain arbitrary integrable real functions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower : ℝ) (T : ℝ≥0) (f : Ω → ℝ)
    (hf : Integrable f P) :
    P[({ω | ∀ t : ℝ≥0, t ≤ T → ¬ X.X t ω < lower}).indicator f | 𝓕 T] =ᵐ[P]
      ({ω | ∀ t : ℝ≥0, t ≤ T → ¬ X.X t ω < lower}).indicator
        (P[f | 𝓕 T]) := by
  have hA : MeasurableSet[𝓕 T]
      {ω | ∀ t : ℝ≥0, t ≤ T → ¬ X.X t ω < lower} :=
    AvramDividend.Classical.chat03_lower_survival_filtration_measurable
      X τ hCover lower T
  exact condExp_indicator hf hA

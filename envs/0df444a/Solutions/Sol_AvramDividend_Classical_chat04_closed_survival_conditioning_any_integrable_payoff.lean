-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_survival_conditioning_any_integrable_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:24:13.662529+00:00
-- url     : https://prove2.me/submissions/a1b2b482-d670-4b92-a7ec-b4c4fd71cf0a

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
A full continuous-time survival event through the closed horizon T is
measurable at T. Its indicator may therefore be extracted from the
conditional expectation of ANY integrable future path-dependent payoff.
This does not assume the future payoff is independent of past survival.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0)
    (f : Ω → ℝ) (hf : Integrable f P) :
    P[({ω | ∀ t : ℝ≥0, t ≤ T →
         ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator f | 𝓕 T] =ᵐ[P]
      ({ω | ∀ t : ℝ≥0, t ≤ T →
         ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
        (P[f | 𝓕 T]) := by
  have hA : MeasurableSet[𝓕 T]
      {ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} :=
    AvramDividend.Classical.chat04_closed_horizon_survival_filtration_measurable
      X τ hCover lower upper T
  exact condExp_indicator hf hA

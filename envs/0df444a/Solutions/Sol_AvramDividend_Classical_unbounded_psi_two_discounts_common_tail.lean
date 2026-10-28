-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_psi_two_discounts_common_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:57:23.416975+00:00
-- url     : https://prove2.me/submissions/b110c711-af80-4bc9-85a0-5fc2840c01aa

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Both scale-function discounts lie below the Laplace exponent on a common
right half-line for a non-bounded-variation spectrally negative process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ q₁ < X.ψ θ ∧ q₂ < X.ψ θ := by
  obtain ⟨β₁, hβ₁, htail₁⟩ :=
    unbounded_psi_discount_denominator_eventually_linear X hnbv q₁ hq₁ 0
  obtain ⟨β₂, hβ₂, htail₂⟩ :=
    unbounded_psi_discount_denominator_eventually_linear X hnbv q₂ hq₂ 0
  refine ⟨max β₁ β₂, ?_, ?_⟩
  · have hβ : β₁ ≤ max β₁ β₂ := le_max_left β₁ β₂
    linarith
  intro θ hθ
  have hθ₁ : β₁ ≤ θ :=
    (le_max_left β₁ β₂).trans (le_of_lt hθ)
  have hθ₂ : β₂ ≤ θ :=
    (le_max_right β₁ β₂).trans (le_of_lt hθ)
  have hψ₁ := htail₁ θ hθ₁
  have hψ₂ := htail₂ θ hθ₂
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · simpa using hψ₁
  · simpa using hψ₂

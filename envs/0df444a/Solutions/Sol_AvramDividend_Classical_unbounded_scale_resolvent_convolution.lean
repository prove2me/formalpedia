-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_resolvent_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:09:30.600991+00:00
-- url     : https://prove2.me/submissions/0d085665-3877-4a5e-982a-ed0bd079736a

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
import Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_scale_integrability
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine two-discount scale resolvent identity for unbounded-variation
paths, with no separately assumed convolution regularity or Laplace tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      W₂ x = W₁ x + (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) := by
  obtain ⟨b, hb, hlarge⟩ :=
    unbounded_psi_two_discounts_common_tail X hnbv q₁ q₂ hq₁ hq₂
  have hanchor : ∃ θ : ℝ, b < θ := by
    refine ⟨b + 1, ?_⟩
    linarith
  exact scale_resolvent_convolution_of_scale_integrability
    X q₁ q₂ b W₁ W₂ hW₁ hW₂ hlarge hanchor

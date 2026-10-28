-- Prove2me | solution 1 for AvramDividend.Classical.withDensity_injective_of_everywhere_pos_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:46:12.594656+00:00
-- url     : https://prove2.me/submissions/e47d2fc4-7dcb-4dc4-beff-7309b7485484

import Mathlib.MeasureTheory.Measure.WithDensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {α : Type} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f)
    (hpos : ∀ x, f x ≠ 0)
    (hfinite : ∀ x, f x ≠ ⊤)
    (heq : μ.withDensity f = ν.withDensity f) : μ = ν := by
  have hμ0 : ∀ᵐ x ∂μ, f x ≠ 0 := ae_of_all μ hpos
  have hμtop : ∀ᵐ x ∂μ, f x ≠ ⊤ := ae_of_all μ hfinite
  have hν0 : ∀ᵐ x ∂ν, f x ≠ 0 := ae_of_all ν hpos
  have hνtop : ∀ᵐ x ∂ν, f x ≠ ⊤ := ae_of_all ν hfinite
  calc
    μ = (μ.withDensity f).withDensity (fun x => (f x)⁻¹) :=
      (withDensity_inv_same hf hμ0 hμtop).symm
    _ = (ν.withDensity f).withDensity (fun x => (f x)⁻¹) :=
      congrArg (fun m : Measure α => m.withDensity (fun x => (f x)⁻¹)) heq
    _ = ν := withDensity_inv_same hf hν0 hνtop
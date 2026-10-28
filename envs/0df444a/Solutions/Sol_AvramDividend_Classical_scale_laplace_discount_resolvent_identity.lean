-- Prove2me | solution 1 for AvramDividend.Classical.scale_laplace_discount_resolvent_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:49:56.127418+00:00
-- url     : https://prove2.me/submissions/7ac7cd1e-76e8-4015-9d0f-408e42516716

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Discounted scale-function Laplace transforms obey the exact two-discount
resolvent identity, the transform-level precursor to the renewal equation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ θ : ℝ) (hθ : 0 ≤ θ)
    (hψ₁ : q₁ < X.ψ θ) (hψ₂ : q₂ < X.ψ θ)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₂ x) -
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₁ x) =
    (q₂ - q₁) *
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₁ x) *
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₂ x) := by
  have hLap₁ := (hW₁.2.2.2.2 θ hθ hψ₁).2
  have hLap₂ := (hW₂.2.2.2.2 θ hθ hψ₂).2
  rw [hLap₁, hLap₂]
  have hne₁ : X.ψ θ - q₁ ≠ 0 := ne_of_gt (sub_pos.mpr hψ₁)
  have hne₂ : X.ψ θ - q₂ ≠ 0 := ne_of_gt (sub_pos.mpr hψ₂)
  field_simp [hne₁, hne₂]
  ring

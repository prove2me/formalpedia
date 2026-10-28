-- Prove2me | solution 2 for AvramDividend.Classical.scale_laplace_discount_resolvent_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:51:13.518606+00:00
-- url     : https://prove2.me/submissions/29b44cd8-9470-426e-bbbe-213f0a3a959d

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
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
  rw [(hW₁.2.2.2.2 θ hθ hψ₁).2, (hW₂.2.2.2.2 θ hθ hψ₂).2]
  have h1 : X.ψ θ - q₁ ≠ 0 := by linarith
  have h2 : X.ψ θ - q₂ ≠ 0 := by linarith
  field_simp
  ring

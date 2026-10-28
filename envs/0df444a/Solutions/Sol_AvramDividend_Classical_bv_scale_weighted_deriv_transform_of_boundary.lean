-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_weighted_deriv_transform_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:03:53.710691+00:00
-- url     : https://prove2.me/submissions/ff1c0abf-0fc6-4aa1-87b5-20d5fe0d4884

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_derivative_with_origin_boundary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The weighted derivative transform retains the nonzero BV scale origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hder : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hLaplace : (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * W x) = (X.ψ θ - q)⁻¹) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * deriv W x) =
    θ * (X.ψ θ - q)⁻¹ - W 0 := by
  have hDint :=
    chat07_scale_weighted_deriv_integrable_positive_halfline
      X q W hW θ hθ hqθ
  have hFTC :=
    weightedLaplace_derivative_with_origin_boundary
      W θ hcont hder hWint hDint
  rw [hFTC, hLaplace]

-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_laplace_compensated_fixed_jump_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:15:37.155764+00:00
-- url     : https://prove2.me/submissions/e5ffc01c-16f9-400d-9199-bcc2855710e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_compensated_fixed_jump
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_derivative_with_origin_boundary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         SpectrallyNegativeLevy.generatorIntegrand W x y) =
      (Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) *
        (X.ψ θ - q)⁻¹ +
      (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) * W 0 := by
  have hWint :
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)) :=
    (hW.2.2.2.2 θ hθ hqθ).1
  have hWlap :
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * W x) = (X.ψ θ - q)⁻¹ :=
    (hW.2.2.2.2 θ hθ hqθ).2
  have hDlap :=
    weightedLaplace_derivative_with_origin_boundary
      W θ hcont hderiv hWint hDint
  calc
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        SpectrallyNegativeLevy.generatorIntegrand W x y) =
      (Real.exp (θ * y) - 1) * (X.ψ θ - q)⁻¹ -
        (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) *
          (∫ x in Ioi (0 : ℝ),
            Real.exp (-(θ * x)) * deriv W x) :=
        scaleFunction_laplace_compensated_fixed_jump X q W hW θ y hθ hqθ hy hDint
    _ = _ := by rw [hDlap, hWlap]; ring

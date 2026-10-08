-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:30:46.982309+00:00
-- url     : https://prove2.me/submissions/c7c4bdab-8a14-4635-ad90-3d0a7eaccd97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_compensated_jump_zero_origin

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
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hzero : W 0 = 0)
    (hkernel : IntegrableOn (fun y : ℝ =>
       Real.exp (θ * y) - 1 -
         θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
       (Iio 0) X.ν)
    (hfubini :
       (∫ x in Ioi (0 : ℝ),
         Real.exp (-(θ * x)) *
           (∫ y in Iio (0 : ℝ),
             SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
       ∫ y in Iio (0 : ℝ),
         (∫ x in Ioi (0 : ℝ),
           Real.exp (-(θ * x)) *
             SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         (∫ y in Iio (0 : ℝ),
           SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      (∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
        ∂X.ν) * (X.ψ θ - q)⁻¹ := by
  rw [hfubini]
  have hpoint : (∫ y in Iio (0 : ℝ),
         (∫ x in Ioi (0 : ℝ),
           Real.exp (-(θ * x)) *
             SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) =
      ∫ y in Iio (0 : ℝ),
        ((Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y)) *
          (X.ψ θ - q)⁻¹) ∂X.ν := by
    apply integral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with y hy
    exact scaleFunction_laplace_compensated_jump_zero_origin
      X q W hW θ y hθ hqθ hy.le hcont hderiv hDint hzero
  rw [hpoint, integral_mul_const]

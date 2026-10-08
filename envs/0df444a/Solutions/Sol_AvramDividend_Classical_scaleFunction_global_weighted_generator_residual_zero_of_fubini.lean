-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_global_weighted_generator_residual_zero_of_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:48:41.450504+00:00
-- url     : https://prove2.me/submissions/c32419c5-606d-45dc-8c8c-ff968808e3d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_gaussian_drift_with_boundary
import Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
import Theorems.Thm_AvramDividend_Classical_gaussian_generator_weighted_residual_vanishes

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
    (θ σ c : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)))
    (hzero : W 0 = 0)
    (horigin : (σ ^ 2 / 2) * deriv W 0 = 1)
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
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν)
    (hpsi : X.ψ θ =
      (σ ^ 2 / 2) * θ ^ 2 + c * θ +
        (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 -
            θ * (y * (Ioo (-1 : ℝ) 1).indicator
              (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν)) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x +
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
          - q * W x)) = 0 := by
  let J : ℝ :=
    ∫ y in Iio (0 : ℝ),
      Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν
  let fD : ℝ → ℝ := fun x =>
    Real.exp (-(θ * x)) *
      ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x)
  let fJ : ℝ → ℝ := fun x =>
    Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
  let fW : ℝ → ℝ := fun x => Real.exp (-(θ * x)) * W x
  have hD2mul : IntegrableOn (fun x : ℝ =>
      (σ ^ 2 / 2) *
        (Real.exp (-(θ * x)) * deriv (deriv W) x)) (Ioi (0 : ℝ)) :=
    hD2int.const_mul (σ ^ 2 / 2)
  have hDmul : IntegrableOn (fun x : ℝ =>
      c * (Real.exp (-(θ * x)) * deriv W x)) (Ioi (0 : ℝ)) :=
    hDint.const_mul c
  have hDgood : IntegrableOn fD (Ioi (0 : ℝ)) := by
    apply (hD2mul.add hDmul).congr
    filter_upwards with x
    dsimp [fD]
    ring
  have hJgood : IntegrableOn fJ (Ioi (0 : ℝ)) := hJint
  have hWgood : IntegrableOn fW (Ioi (0 : ℝ)) := hWint
  have hWtr : (∫ x in Ioi (0 : ℝ), fW x) =
      (X.ψ θ - q)⁻¹ := (hW.2.2.2.2 θ hθ hqθ).2
  have hDtr : (∫ x in Ioi (0 : ℝ), fD x) =
      ((σ ^ 2 / 2) * θ ^ 2 + c * θ) * (X.ψ θ - q)⁻¹ -
        (σ ^ 2 / 2) * deriv W 0 := by
    have h := weightedLaplace_gaussian_drift_with_boundary
      W θ σ c hcont hderiv hcont1 hderiv1 hWint hDint hD2int
    change (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x)) = _ 
    rw [h, hWtr, hzero]
    ring
  have hJtr : (∫ x in Ioi (0 : ℝ), fJ x) =
      J * (X.ψ θ - q)⁻¹ := by
    exact scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
      X q W hW θ hθ hqθ hcont hderiv hDint hzero hkernel hfubini
  have hpsiJ : X.ψ θ = (σ ^ 2 / 2) * θ ^ 2 + c * θ + J := hpsi
  have hz : (∫ x in Ioi (0 : ℝ), fD x + fJ x - q * fW x) = 0 :=
    gaussian_generator_weighted_residual_vanishes
      fD fJ fW (σ ^ 2 / 2) c θ q (X.ψ θ) J (deriv W 0)
      hDgood hJgood hWgood hDtr hJtr hWtr hpsiJ hqθ horigin
  calc
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x +
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
          - q * W x)) =
      ∫ x in Ioi (0 : ℝ), fD x + fJ x - q * fW x := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [fD, fJ, fW]
        ring
    _ = 0 := hz

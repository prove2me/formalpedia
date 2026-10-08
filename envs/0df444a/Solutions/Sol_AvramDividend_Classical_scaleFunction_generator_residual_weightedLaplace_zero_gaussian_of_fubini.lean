-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:38:41.226963+00:00
-- url     : https://prove2.me/submissions/9139330c-ea40-41e7-83bf-e103891b09f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_gaussian_drift_with_boundary
import Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
import Theorems.Thm_AvramDividend_Classical_levy_gaussian_laplace_cancellation_of_origin_normalization


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
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hzero : W 0 = 0)
    (horigin : (X.σ ^ 2 / 2) * deriv W 0 = 1)
    (hkernel : IntegrableOn (fun y : ℝ =>
       Real.exp (θ * y) - 1 -
         θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
       (Iio 0) X.ν)
    (hGint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) *
         ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x))
       (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) *
         (∫ y in Iio (0 : ℝ),
           SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
       (Ioi (0 : ℝ)))
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
       Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by
  let F : ℝ := (X.ψ θ - q)⁻¹
  let d : ℝ := X.σ ^ 2 / 2
  let J : ℝ := ∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν
  have hWint : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x)
      (Ioi (0 : ℝ)) := (hW.2.2.2.2 θ hθ hqθ).1
  have hWtr : (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * W x) = F :=
    (hW.2.2.2.2 θ hθ hqθ).2
  have hGtr := weightedLaplace_gaussian_drift_with_boundary
    W θ X.σ X.c hcont hderiv hcont1 hderiv1 hWint hDint hD2int
  have hJtr := scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
    X q W hW θ hθ hqθ hcont hderiv hDint hzero hkernel hfubini
  have hD2eq (x : ℝ) :
      iteratedDeriv 2 W x = deriv (deriv W) x := by
    have h :=
      congrFun (iteratedDeriv_succ (f := W) (n := 1)) x
    simpa only [iteratedDeriv_one] using h
  have hJ_eq : (∫ y in Iio (0 : ℝ),
      Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν) = J := by
    apply setIntegral_congr_fun measurableSet_Iio
    intro y hy
    dsimp [J]
    ring
  calc
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * (X.generator W x - q * W x)) =
      ∫ x in Ioi (0 : ℝ),
        (Real.exp (-(θ * x)) *
          (d * deriv (deriv W) x + X.c * deriv W x) +
         Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
         q * (Real.exp (-(θ * x)) * W x)) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [SpectrallyNegativeLevy.generator, d]
          rw [hD2eq x]
          ring
    _ = (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (d * deriv (deriv W) x + X.c * deriv W x)) +
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
           (∫ y in Iio (0 : ℝ),
             SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) -
        q * (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) * W x) := by
            have hsplit :=
              integral_sub (hGint.add hJint) (hWint.const_mul q)
            have hadd := integral_add hGint hJint
            simpa only [Pi.add_apply, Pi.sub_apply, hadd, integral_const_mul] using hsplit
    _ = (d * θ ^ 2 + X.c * θ + J - q) * F -
        d * deriv W 0 := by
          rw [hGtr, hJtr, hWtr, hJ_eq, hzero]
          dsimp [d, F]
          ring
    _ = 0 := by
      exact levy_gaussian_laplace_cancellation_of_origin_normalization
        X q θ (deriv W 0) hqθ horigin

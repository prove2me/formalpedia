-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_weighted_generator_residual_integral_zero_of_full_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:32:37.574391+00:00
-- url     : https://prove2.me/submissions/86f27538-d080-4faa-8c5a-b12ebe777a1f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_gaussian_drift_with_boundary
import Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
import Theorems.Thm_AvramDividend_Classical_gaussian_generator_weighted_residual_vanishes
import Theorems.Thm_AvramDividend_Classical_iteratedDeriv_two_eq_deriv_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The weighted Laplace transform of the generator residual of the scale function
vanishes.

This is the general step of the core analytic obligation of Lemma 4 of Avram:
the scale function identity `∫ e^{-θ y} W y dy = (ψ θ - q)⁻¹` gives the
vanishing of the weighted transform of the residual `(Γ - q) W`, once the
generator is split into its Gaussian-and-drift part and its jump part and the
two transforms are evaluated.

The Gaussian-and-drift part is evaluated by
`weightedLaplace_gaussian_drift_with_boundary`, the jump part by
`scaleFunction_laplace_integrated_jump_zero_origin_of_fubini`, and the two
are combined by `gaussian_generator_weighted_residual_vanishes`, whose last
input is the origin normalisation `(σ²/2) W'(0) = 1`.

This is the same argument as the Proved theorem
`scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini`
(`c1dd9ab6`), with one difference: that theorem assumes the integrability of
the Gaussian-and-drift part, whereas here it is *derived* from the
integrability of `e^{-θ x} W'(x)` and of `e^{-θ x} W''(x)`.
-/

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
    (hJint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)))
    (hkernel : IntegrableOn (fun y : ℝ =>
      Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y)) (Iio 0) X.ν)
    (hfubini :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν)
    (hzero : W 0 = 0)
    (hψ : X.ψ θ =
      (X.σ ^ 2 / 2) * θ ^ 2 + X.c * θ +
      ∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν)
    (horigin : (X.σ ^ 2 / 2) * deriv W 0 = 1) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by
  let fD : ℝ → ℝ := fun x =>
    Real.exp (-(θ * x)) *
      ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x)
  let fJ : ℝ → ℝ := fun x =>
    Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
  let fW : ℝ → ℝ := fun x => Real.exp (-(θ * x)) * W x
  let J : ℝ :=
    ∫ y in Iio (0 : ℝ),
      Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν
  have hWint : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x)
      (Ioi (0 : ℝ)) := (hW.2.2.2.2 θ hθ hqθ).1
  have hWtr : (∫ x in Ioi (0 : ℝ), fW x) =
      (X.ψ θ - q)⁻¹ := (hW.2.2.2.2 θ hθ hqθ).2
  -- The integrability of the Gaussian-and-drift part follows from the
  -- integrability of the two derivatives.
  have hD2mul : IntegrableOn (fun x : ℝ =>
      (X.σ ^ 2 / 2) *
        (Real.exp (-(θ * x)) * deriv (deriv W) x)) (Ioi (0 : ℝ)) :=
    hD2int.const_mul (X.σ ^ 2 / 2)
  have hDmul : IntegrableOn (fun x : ℝ =>
      X.c * (Real.exp (-(θ * x)) * deriv W x)) (Ioi (0 : ℝ)) :=
    hDint.const_mul X.c
  have hDgood : IntegrableOn fD (Ioi (0 : ℝ)) := by
    apply (hD2mul.add hDmul).congr
    filter_upwards with x
    dsimp [fD]
    ring
  have hJgood : IntegrableOn fJ (Ioi (0 : ℝ)) := hJint
  have hWgood : IntegrableOn fW (Ioi (0 : ℝ)) := hWint
  -- The weighted transform of the Gaussian-and-drift part, with the
  -- boundary terms at the origin.
  have hDtr : (∫ x in Ioi (0 : ℝ), fD x) =
      ((X.σ ^ 2 / 2) * θ ^ 2 + X.c * θ) * (X.ψ θ - q)⁻¹ -
        (X.σ ^ 2 / 2) * deriv W 0 := by
    have h := weightedLaplace_gaussian_drift_with_boundary
      W θ X.σ X.c hcont hderiv hcont1 hderiv1 hWint hDint hD2int
    change (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x)) = _
    rw [h, hWtr, hzero]
    ring
  -- The weighted transform of the jump part, by the Fubini identity.
  have hJtr : (∫ x in Ioi (0 : ℝ), fJ x) =
      J * (X.ψ θ - q)⁻¹ := by
    exact scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
      X q W hW θ hθ hqθ hcont hderiv hDint hzero hkernel hfubini
  have hpsiJ : X.ψ θ = (X.σ ^ 2 / 2) * θ ^ 2 + X.c * θ + J := by
    exact hψ
  -- The three transforms combine, and the origin normalisation cancels the
  -- residual term.
  have hz : (∫ x in Ioi (0 : ℝ), fD x + fJ x - q * fW x) = 0 :=
    gaussian_generator_weighted_residual_vanishes
      fD fJ fW (X.σ ^ 2 / 2) X.c θ q (X.ψ θ) J (deriv W 0)
      hDgood hJgood hWgood hDtr hJtr hWtr hpsiJ hqθ horigin
  calc
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (X.generator W x - q * W x)) =
      ∫ x in Ioi (0 : ℝ), fD x + fJ x - q * fW x := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [fD, fJ, fW]
        unfold SpectrallyNegativeLevy.generator
        rw [iteratedDeriv_two_eq_deriv_deriv W x]
        ring
    _ = 0 := hz

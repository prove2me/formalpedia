-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_residual_weightedLaplace_zero_gaussian_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:19:52.682822+00:00
-- url     : https://prove2.me/submissions/799616b2-1807-4704-b224-baab38548c61

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The whole family of weighted Laplace transforms of the Gaussian q-scale
generator residual vanishes.

A single Laplace parameter does not identify the residual; the uniqueness
theorem for the Laplace transform needs a family.  The Proved theorem
`scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini`
gives the vanishing of the weighted residual transform for an arbitrary
admissible parameter, so instantiating it at each admissible parameter gives
the whole family.  The integrability of the weighted residual follows from the
integrability of its pieces: the discounted Gaussian and drift term, the
discounted compensated jump term, and the discounted scale function.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hzero : W 0 = 0)
    (horigin : (X.σ ^ 2 / 2) * deriv W 0 = 1)
    (hkernel : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun y : ℝ =>
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y))
        (Iio (0 : ℝ)) X.ν)
    (hDint : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hGint : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) *
          ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x))
        (Ioi (0 : ℝ)))
    (hJint : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
        (Ioi (0 : ℝ)))
    (hfubini : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :
    ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by
  intro θ hθ hqθ
  -- The weighted residual transform vanishes: this is the Proved single
  -- parameter statement, instantiated at the given parameter.
  have hvanish :
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 :=
    scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini
      X q W hW θ hθ hqθ hcont hderiv hcont1 hderiv1
      (hDint θ hθ hqθ) (hD2int θ hθ hqθ) hzero horigin
      (hkernel θ hθ hqθ) (hGint θ hθ hqθ) (hJint θ hθ hqθ)
      (hfubini θ hθ hqθ)
  -- The discounted scale function is integrable: it is one of the terms of
  -- the discounted Gaussian and drift integrand, up to the constant `q`.
  have hWint : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W x)
      (Ioi (0 : ℝ)) := (hW.2.2.2.2 θ hθ hqθ).1
  -- The discounted residual decomposes into the discounted Gaussian and drift
  -- term, the discounted compensated jump term, and the discounted scale
  -- function; each of the three is integrable.
  have hres : (fun x : ℝ => Real.exp (-(θ * x)) * (X.generator W x - q * W x)) =
      (fun x : ℝ => Real.exp (-(θ * x)) *
        ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x) +
       Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
       Real.exp (-(θ * x)) * (q * W x)) := by
    funext x
    dsimp [SpectrallyNegativeLevy.generator]
    have hD2eq : iteratedDeriv 2 W x = deriv (deriv W) x := by
      have h := congrFun (iteratedDeriv_succ (f := W) (n := 1)) x
      simpa only [iteratedDeriv_one] using h
    rw [hD2eq]
    ring
  have hWq : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * (q * W x))
      (Ioi (0 : ℝ)) := by
    -- The discounted scale function is integrable on the positive half-line,
    -- and the integrand is that function multiplied by the constant `q`.
    have h := hWint.mul_const q
    have h' : Integrable (fun x : ℝ => (Real.exp (-(θ * x)) * W x) * q)
        ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := h
    rw [← show (fun x : ℝ => Real.exp (-(θ * x)) * (q * W x)) =
        (fun x : ℝ => (Real.exp (-(θ * x)) * W x) * q) from
      by funext x; ring] at h'
    exact h'
  have hparts :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x)) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * (q * W x)) (Ioi (0 : ℝ)) :=
    ⟨hGint θ hθ hqθ, hJint θ hθ hqθ, hWq⟩
  have hinter : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (X.generator W x - q * W x)) (Ioi (0 : ℝ)) := by
    rw [hres]
    exact (hparts.1.add hparts.2.1).sub hparts.2.2
  exact ⟨hinter, hvanish⟩

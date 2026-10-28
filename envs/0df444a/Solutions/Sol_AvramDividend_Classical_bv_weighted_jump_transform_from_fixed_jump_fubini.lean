-- Prove2me | solution 1 for AvramDividend.Classical.bv_weighted_jump_transform_from_fixed_jump_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:00:32.952124+00:00
-- url     : https://prove2.me/submissions/5d0b293c-c132-4a83-b857-ef295cfcf0a7

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_compensated_fixed_jump_boundary
import Theorems.Thm_AvramDividend_Classical_weighted_jump_integral_affine_compensation
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Fubini and the fixed-jump Laplace identity give the exact BV jump transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hder : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hprod : Integrable
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))))
    (hExp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν)
    (hK : IntegrableOn
      (fun y : ℝ =>
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
      (Iio (0 : ℝ)) X.ν)
    (hKvalue : (∫ y in Iio (0 : ℝ),
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y ∂X.ν) =
      X.c - X.drift) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
    (∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 ∂X.ν) *
        (X.ψ θ - q)⁻¹ -
      θ * (X.c - X.drift) * (X.ψ θ - q)⁻¹ +
      (X.c - X.drift) * W 0 := by
  have hfubini :=
    scaleFunction_generator_weighted_global_fubini_of_prod_integrable
      X W θ hprod
  have hfixed :
      (∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) =
      (∫ y in Iio (0 : ℝ),
        ((Real.exp (θ * y) - 1 -
            θ * (y * (Ioo (-1 : ℝ) 1).indicator
              (fun _ : ℝ => (1 : ℝ)) y)) *
            (X.ψ θ - q)⁻¹ +
          (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) * W 0) ∂X.ν) := by
    apply setIntegral_congr_fun measurableSet_Iio
    intro y hy
    exact scaleFunction_laplace_compensated_fixed_jump_boundary
      X q W hW θ y hθ hqθ (le_of_lt hy) hcont hder hDint
  have haffine :=
    weighted_jump_integral_affine_compensation
      (X.ν.restrict (Iio (0 : ℝ)))
      (fun y : ℝ => Real.exp (θ * y) - 1)
      (fun y : ℝ =>
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
      θ (X.ψ θ - q)⁻¹ (W 0) hExp hK
  calc
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      (∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :=
      hfubini
    _ = (∫ y in Iio (0 : ℝ),
        ((Real.exp (θ * y) - 1 -
            θ * (y * (Ioo (-1 : ℝ) 1).indicator
              (fun _ : ℝ => (1 : ℝ)) y)) *
            (X.ψ θ - q)⁻¹ +
          (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) * W 0) ∂X.ν) :=
      hfixed
    _ = (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) *
          (X.ψ θ - q)⁻¹ -
        θ * (X.c - X.drift) * (X.ψ θ - q)⁻¹ +
        (X.c - X.drift) * W 0 := by
      rw [haffine, hKvalue]
      ring

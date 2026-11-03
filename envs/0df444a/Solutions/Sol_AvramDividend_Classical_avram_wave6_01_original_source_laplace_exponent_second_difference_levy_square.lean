-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_source_laplace_exponent_second_difference_levy_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:47:42.082124+00:00
-- url     : https://prove2.me/submissions/85f87f85-d6d8-40a7-9a42-e3f323c458aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine Lévy exponent's quadratic finite difference identifies source jump variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ (2 * θ) - 2 * X.ψ θ =
      X.σ ^ 2 * θ ^ 2 +
        ∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ^ 2 ∂X.ν := by
  classical
  let g : ℝ → ℝ → ℝ := fun r y =>
    Real.exp (r * y) - 1 -
      r * y * (Ioo (-1 : ℝ) 1).indicator 1 y
  have hweight : IntegrableOn
      (fun y : ℝ => min 1 (y ^ 2)) (Iio (0 : ℝ)) X.ν :=
    (levyWeight_integrable X).integrableOn
  have hint (r : ℝ) (hr : 0 ≤ r) :
      IntegrableOn (g r) (Iio (0 : ℝ)) X.ν := by
    have h := levy_exponential_generatorIntegrable_of_moment
      X r 0 hr hweight
    change IntegrableOn
      (fun y : ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => Real.exp (r * z)) 0 y)
      (Iio (0 : ℝ)) X.ν at h
    simpa only [g, generatorIntegrand_exp_mul, mul_zero,
      Real.exp_zero, one_mul] using h
  have hint1 := hint θ hθ
  have hint2 := hint (2 * θ) (mul_nonneg (by norm_num) hθ)
  have hpoint (y : ℝ) :
      g (2 * θ) y - 2 * g θ y =
        (Real.exp (θ * y) - 1) ^ 2 := by
    have he : Real.exp ((2 * θ) * y) =
        Real.exp (θ * y) * Real.exp (θ * y) := by
      rw [show (2 * θ) * y = θ * y + θ * y by ring, Real.exp_add]
    dsimp [g]
    rw [he]
    ring
  have hν :
      (∫ y in Iio (0 : ℝ), g (2 * θ) y ∂X.ν) -
          2 * (∫ y in Iio (0 : ℝ), g θ y ∂X.ν) =
        ∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ^ 2 ∂X.ν := by
    calc
      _ = ∫ y in Iio (0 : ℝ), (g (2 * θ) y - 2 * g θ y) ∂X.ν := by
        rw [integral_sub hint2 (hint1.const_mul 2)]
        simp only [integral_const_mul, smul_eq_mul]
      _ = ∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ^ 2 ∂X.ν := by
        have hf :
            (fun y : ℝ => g (2 * θ) y - 2 * g θ y) =
            (fun y : ℝ => (Real.exp (θ * y) - 1) ^ 2) :=
          funext hpoint
        rw [hf]
  change
    (X.c * (2 * θ) + X.σ ^ 2 * (2 * θ) ^ 2 / 2 +
      (∫ y in Iio (0 : ℝ), g (2 * θ) y ∂X.ν)) -
    2 * (X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ y in Iio (0 : ℝ), g θ y ∂X.ν)) =
    X.σ ^ 2 * θ ^ 2 +
      ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 2 ∂X.ν
  calc
    _ = X.σ ^ 2 * θ ^ 2 +
        ((∫ y in Iio (0 : ℝ), g (2 * θ) y ∂X.ν) -
          2 * (∫ y in Iio (0 : ℝ), g θ y ∂X.ν)) := by ring
    _ = _ := by rw [hν]

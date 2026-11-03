-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_source_laplace_exponent_fourth_difference_jump_fourth_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:50:52.767197+00:00
-- url     : https://prove2.me/submissions/a15791ba-58bc-4a03-a139-a521a1e6bdd4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ (4 * θ) - 4 * X.ψ (3 * θ) + 6 * X.ψ (2 * θ) - 4 * X.ψ θ =
      ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by
  classical
  let g : ℝ → ℝ → ℝ := fun r y => Real.exp (r * y) - 1 -
    r * y * (Ioo (-1 : ℝ) 1).indicator 1 y
  have hw : IntegrableOn (fun y : ℝ => min 1 (y ^ 2)) (Iio (0 : ℝ)) X.ν :=
    (levyWeight_integrable X).integrableOn
  have hint (r : ℝ) (hr : 0 ≤ r) : IntegrableOn (g r) (Iio (0 : ℝ)) X.ν := by
    have h := levy_exponential_generatorIntegrable_of_moment X r 0 hr hw
    change IntegrableOn (fun y : ℝ =>
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => Real.exp (r * z)) 0 y) (Iio (0 : ℝ)) X.ν at h
    simpa only [g, generatorIntegrand_exp_mul, mul_zero,
      Real.exp_zero, one_mul] using h
  have h1 := hint θ hθ
  have h2 := hint (2 * θ) (mul_nonneg (by norm_num) hθ)
  have h3 := hint (3 * θ) (mul_nonneg (by norm_num) hθ)
  have h4 := hint (4 * θ) (mul_nonneg (by norm_num) hθ)
  have hp (y : ℝ) : g (4 * θ) y - 4 * g (3 * θ) y + 6 * g (2 * θ) y - 4 * g θ y = (Real.exp (θ * y) - 1) ^ 4 := by
    have e2 : Real.exp ((2 * θ) * y) = Real.exp (θ * y) ^ 2 := by
      rw [show (2 * θ) * y = θ * y + θ * y by ring, Real.exp_add]
      ring
    have e3 : Real.exp ((3 * θ) * y) = Real.exp (θ * y) ^ 3 := by
      rw [show (3 * θ) * y = (θ * y + θ * y) + θ * y by ring, Real.exp_add, Real.exp_add]
      ring
    have e4 : Real.exp ((4 * θ) * y) = Real.exp (θ * y) ^ 4 := by
      rw [show (4 * θ) * y = (θ * y + θ * y) + (θ * y + θ * y) by ring]
      simp only [Real.exp_add]; ring
    dsimp [g]
    rw [e2, e3, e4]
    ring
  have hj : (∫ y in Iio (0 : ℝ), g (4 * θ) y ∂X.ν) -
      4 * (∫ y in Iio (0 : ℝ), g (3 * θ) y ∂X.ν) +
      6 * (∫ y in Iio (0 : ℝ), g (2 * θ) y ∂X.ν) -
      4 * (∫ y in Iio (0 : ℝ), g θ y ∂X.ν) =
      ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by
    have h43 : (∫ y in Iio (0 : ℝ), g (4 * θ) y ∂X.ν) -
        4 * (∫ y in Iio (0 : ℝ), g (3 * θ) y ∂X.ν) =
        ∫ y in Iio (0 : ℝ), (g (4 * θ) y - 4 * g (3 * θ) y) ∂X.ν := by
      rw [← integral_const_mul]
      simpa only [Pi.sub_apply] using (integral_sub h4 (h3.const_mul 4)).symm
    have h432 : (∫ y in Iio (0 : ℝ), (g (4 * θ) y - 4 * g (3 * θ) y) ∂X.ν) +
        6 * (∫ y in Iio (0 : ℝ), g (2 * θ) y ∂X.ν) =
        ∫ y in Iio (0 : ℝ), (g (4 * θ) y - 4 * g (3 * θ) y + 6 * g (2 * θ) y) ∂X.ν := by
      rw [← integral_const_mul]
      simpa only [Pi.sub_apply, Pi.add_apply] using
        (integral_add (h4.sub (h3.const_mul 4)) (h2.const_mul 6)).symm
    have h4321 : (∫ y in Iio (0 : ℝ), (g (4 * θ) y - 4 * g (3 * θ) y + 6 * g (2 * θ) y) ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g θ y ∂X.ν) =
        ∫ y in Iio (0 : ℝ), (g (4 * θ) y - 4 * g (3 * θ) y + 6 * g (2 * θ) y - 4 * g θ y) ∂X.ν := by
      rw [← integral_const_mul]
      simpa only [Pi.sub_apply, Pi.add_apply] using
        (integral_sub ((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)) (h1.const_mul 4)).symm
    calc
      _ = ∫ y in Iio (0 : ℝ),
          (g (4 * θ) y - 4 * g (3 * θ) y + 6 * g (2 * θ) y - 4 * g θ y) ∂X.ν := by
        rw [h43, h432, h4321]
      _ = ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by
        have he : (fun y : ℝ => g (4 * θ) y - 4 * g (3 * θ) y +
          6 * g (2 * θ) y - 4 * g θ y) =
          (fun y : ℝ => (Real.exp (θ * y) - 1) ^ 4) := funext hp
        rw [he]
  change (X.c * (4 * θ) + X.σ ^ 2 * (4 * θ) ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g (4 * θ) y ∂X.ν)) -
    4 * (X.c * (3 * θ) + X.σ ^ 2 * (3 * θ) ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g (3 * θ) y ∂X.ν)) +
    6 * (X.c * (2 * θ) + X.σ ^ 2 * (2 * θ) ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g (2 * θ) y ∂X.ν)) -
    4 * (X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g θ y ∂X.ν)) =
    ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν
  calc
    _ = (∫ y in Iio (0 : ℝ), g (4 * θ) y ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g (3 * θ) y ∂X.ν) +
        6 * (∫ y in Iio (0 : ℝ), g (2 * θ) y ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g θ y ∂X.ν) := by ring
    _ = _ := hj

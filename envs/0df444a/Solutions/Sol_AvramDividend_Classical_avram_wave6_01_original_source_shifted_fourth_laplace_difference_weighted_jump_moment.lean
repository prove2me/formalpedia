-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_source_shifted_fourth_laplace_difference_weighted_jump_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:27:59.576544+00:00
-- url     : https://prove2.me/submissions/b22e4b89-18a2-47a3-9858-24df71767fc0

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
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    X.ψ (ρ + 4 * θ) - 4 * X.ψ (ρ + 3 * θ) +
      6 * X.ψ (ρ + 2 * θ) - 4 * X.ψ (ρ + θ) + X.ψ ρ =
      ∫ y in Iio (0 : ℝ), Real.exp (ρ * y) *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by
  classical
  let g : ℝ → ℝ → ℝ := fun r y => Real.exp (r * y) - 1 -
    r * y * (Ioo (-1 : ℝ) 1).indicator 1 y
  have hw : IntegrableOn (fun y : ℝ => min 1 (y ^ 2)) (Iio (0 : ℝ)) X.ν :=
    (levyWeight_integrable X).integrableOn
  have hint (r : ℝ) (hr : 0 ≤ r) : IntegrableOn (g r) (Iio (0 : ℝ)) X.ν := by
    have h := levy_exponential_generatorIntegrable_of_moment X r 0 hr hw
    change IntegrableOn (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => Real.exp (r * z)) 0 y) (Iio (0 : ℝ)) X.ν at h
    simpa only [g, generatorIntegrand_exp_mul, mul_zero, Real.exp_zero, one_mul] using h
  have h0 := hint ρ hρ
  have h1 := hint (ρ + θ) (add_nonneg hρ hθ)
  have h2 := hint (ρ + 2 * θ) (add_nonneg hρ (mul_nonneg (by norm_num) hθ))
  have h3 := hint (ρ + 3 * θ) (add_nonneg hρ (mul_nonneg (by norm_num) hθ))
  have h4 := hint (ρ + 4 * θ) (add_nonneg hρ (mul_nonneg (by norm_num) hθ))
  have hp (y : ℝ) : g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y + 6 * g (ρ + 2 * θ) y - 4 * g (ρ + θ) y + g ρ y =
      Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4 := by
    have e1 : Real.exp ((ρ + θ) * y) = Real.exp (ρ * y) * Real.exp (θ * y) := by rw [add_mul, Real.exp_add]
    have e2 : Real.exp ((ρ + 2 * θ) * y) = Real.exp (ρ * y) * Real.exp (θ * y) ^ 2 := by
      rw [show (ρ + 2 * θ) * y = ρ * y + (θ * y + θ * y) by ring, Real.exp_add, Real.exp_add]; ring
    have e3 : Real.exp ((ρ + 3 * θ) * y) = Real.exp (ρ * y) * Real.exp (θ * y) ^ 3 := by
      rw [show (ρ + 3 * θ) * y = ρ * y + ((θ * y + θ * y) + θ * y) by ring]; simp only [Real.exp_add]; ring
    have e4 : Real.exp ((ρ + 4 * θ) * y) = Real.exp (ρ * y) * Real.exp (θ * y) ^ 4 := by
      rw [show (ρ + 4 * θ) * y = ρ * y + ((θ * y + θ * y) + (θ * y + θ * y)) by ring]; simp only [Real.exp_add]; ring
    dsimp [g]
    rw [e1, e2, e3, e4]
    ring
  have h43 : (∫ y in Iio (0 : ℝ), g (ρ + 4 * θ) y ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g (ρ + 3 * θ) y ∂X.ν) =
      ∫ y in Iio (0 : ℝ), (g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y) ∂X.ν := by
    rw [← integral_const_mul]
    simpa only [Pi.sub_apply] using (integral_sub h4 (h3.const_mul 4)).symm
  have h432 : (∫ y in Iio (0 : ℝ), (g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y) ∂X.ν) + 6 * (∫ y in Iio (0 : ℝ), g (ρ + 2 * θ) y ∂X.ν) =
      ∫ y in Iio (0 : ℝ), (g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y + 6 * g (ρ + 2 * θ) y) ∂X.ν := by
    rw [← integral_const_mul]
    simpa only [Pi.sub_apply, Pi.add_apply] using
      (integral_add (h4.sub (h3.const_mul 4)) (h2.const_mul 6)).symm
  have h4321 : (∫ y in Iio (0 : ℝ), (g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y + 6 * g (ρ + 2 * θ) y) ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g (ρ + θ) y ∂X.ν) =
      ∫ y in Iio (0 : ℝ), (g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y + 6 * g (ρ + 2 * θ) y - 4 * g (ρ + θ) y) ∂X.ν := by
    rw [← integral_const_mul]
    simpa only [Pi.sub_apply, Pi.add_apply] using
      (integral_sub ((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)) (h1.const_mul 4)).symm
  have h43210 : (∫ y in Iio (0 : ℝ), (g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y + 6 * g (ρ + 2 * θ) y - 4 * g (ρ + θ) y) ∂X.ν) + (∫ y in Iio (0 : ℝ), g ρ y ∂X.ν) =
      ∫ y in Iio (0 : ℝ), (g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y + 6 * g (ρ + 2 * θ) y - 4 * g (ρ + θ) y + g ρ y) ∂X.ν := by
    simpa only [Pi.sub_apply, Pi.add_apply] using
      (integral_add (((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)).sub
        (h1.const_mul 4)) h0).symm
  have hj : (∫ y in Iio (0 : ℝ), g (ρ + 4 * θ) y ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g (ρ + 3 * θ) y ∂X.ν) + 6 * (∫ y in Iio (0 : ℝ), g (ρ + 2 * θ) y ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g (ρ + θ) y ∂X.ν) + (∫ y in Iio (0 : ℝ), g ρ y ∂X.ν) =
      ∫ y in Iio (0 : ℝ), Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by
    calc
      _ = ∫ y in Iio (0 : ℝ), (g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y + 6 * g (ρ + 2 * θ) y - 4 * g (ρ + θ) y + g ρ y) ∂X.ν := by
        rw [h43, h432, h4321, h43210]
      _ = _ := by
        have he : (fun y : ℝ => g (ρ + 4 * θ) y - 4 * g (ρ + 3 * θ) y + 6 * g (ρ + 2 * θ) y - 4 * g (ρ + θ) y + g ρ y) =
          (fun y : ℝ => Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4) := funext hp
        rw [he]
  change (X.c * (ρ + 4 * θ) + X.σ ^ 2 * (ρ + 4 * θ) ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g (ρ + 4 * θ) y ∂X.ν)) -
    4 * (X.c * (ρ + 3 * θ) + X.σ ^ 2 * (ρ + 3 * θ) ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g (ρ + 3 * θ) y ∂X.ν)) +
    6 * (X.c * (ρ + 2 * θ) + X.σ ^ 2 * (ρ + 2 * θ) ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g (ρ + 2 * θ) y ∂X.ν)) -
    4 * (X.c * (ρ + θ) + X.σ ^ 2 * (ρ + θ) ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g (ρ + θ) y ∂X.ν)) +
    (X.c * ρ + X.σ ^ 2 * ρ ^ 2 / 2 + (∫ y in Iio (0 : ℝ), g ρ y ∂X.ν)) =
    ∫ y in Iio (0 : ℝ), Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4 ∂X.ν
  calc
    _ = (∫ y in Iio (0 : ℝ), g (ρ + 4 * θ) y ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g (ρ + 3 * θ) y ∂X.ν) +
        6 * (∫ y in Iio (0 : ℝ), g (ρ + 2 * θ) y ∂X.ν) - 4 * (∫ y in Iio (0 : ℝ), g (ρ + θ) y ∂X.ν) +
        (∫ y in Iio (0 : ℝ), g ρ y ∂X.ν) := by ring
    _ = _ := hj

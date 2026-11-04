-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:45:32.67889+00:00
-- url     : https://prove2.me/submissions/9f1504c7-114c-47fe-bcc0-c69e40940669

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    IntegrableOn
      (fun y : ℝ => Real.exp (ρ * y) *
        (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) X.ν := by
  classical
  let g : ℝ → ℝ → ℝ := fun r y =>
    Real.exp (r * y) - 1 -
      r * y * (Ioo (-1 : ℝ) 1).indicator 1 y
  have hw : IntegrableOn (fun y : ℝ => min 1 (y ^ 2))
      (Iio (0 : ℝ)) X.ν :=
    (levyWeight_integrable X).integrableOn
  have hint (r : ℝ) (hr : 0 ≤ r) :
      IntegrableOn (g r) (Iio (0 : ℝ)) X.ν := by
    have h := levy_exponential_generatorIntegrable_of_moment X r 0 hr hw
    change IntegrableOn (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => Real.exp (r * z)) 0 y) (Iio (0 : ℝ)) X.ν at h
    simpa only [g, generatorIntegrand_exp_mul, mul_zero,
      Real.exp_zero, one_mul] using h
  have h0 := hint ρ hρ
  have h1 := hint (ρ + θ) (add_nonneg hρ hθ)
  have h2 := hint (ρ + 2 * θ)
    (add_nonneg hρ (mul_nonneg (by norm_num) hθ))
  have h3 := hint (ρ + 3 * θ)
    (add_nonneg hρ (mul_nonneg (by norm_num) hθ))
  have h4 := hint (ρ + 4 * θ)
    (add_nonneg hρ (mul_nonneg (by norm_num) hθ))
  have hcombo :=
    (((h4.sub (h3.const_mul (4 : ℝ))).add
      (h2.const_mul (6 : ℝ))).sub
      (h1.const_mul (4 : ℝ))).add h0
  refine hcombo.congr (Filter.Eventually.of_forall (fun y => ?_))
  have e1 : Real.exp ((ρ + θ) * y) =
      Real.exp (ρ * y) * Real.exp (θ * y) := by
    rw [add_mul, Real.exp_add]
  have e2 : Real.exp ((ρ + 2 * θ) * y) =
      Real.exp (ρ * y) * Real.exp (θ * y) ^ 2 := by
    rw [show (ρ + 2 * θ) * y = ρ * y + (θ * y + θ * y) by ring,
      Real.exp_add, Real.exp_add]
    ring
  have e3 : Real.exp ((ρ + 3 * θ) * y) =
      Real.exp (ρ * y) * Real.exp (θ * y) ^ 3 := by
    rw [show (ρ + 3 * θ) * y =
      ρ * y + ((θ * y + θ * y) + θ * y) by ring]
    simp only [Real.exp_add]
    ring
  have e4 : Real.exp ((ρ + 4 * θ) * y) =
      Real.exp (ρ * y) * Real.exp (θ * y) ^ 4 := by
    rw [show (ρ + 4 * θ) * y =
      ρ * y + ((θ * y + θ * y) + (θ * y + θ * y)) by ring]
    simp only [Real.exp_add]
    ring
  dsimp [g]
  rw [e1, e2, e3, e4]
  ring

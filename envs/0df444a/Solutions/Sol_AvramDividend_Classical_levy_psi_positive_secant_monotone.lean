-- Prove2me | solution 1 for AvramDividend.Classical.levy_psi_positive_secant_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T14:37:41.255599+00:00
-- url     : https://prove2.me/submissions/230b19e6-02e6-40c4-9578-dcfbae161017

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_negative_secant_mono
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The origin-based secant of a spectrally negative Lévy exponent is monotone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) :
    X.ψ θ₁ / θ₁ ≤ X.ψ θ₂ / θ₂ := by
  let J : ℝ → ℝ → ℝ := fun θ y =>
    Real.exp (θ * y) - 1 -
      θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
  let K : ℝ → ℝ → ℝ := fun θ y => J θ y / θ
  have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ hθ
  have hi (θ : ℝ) (hθ : 0 ≤ θ) :
      Integrable (J θ) (X.ν.restrict (Iio (0 : ℝ))) := by
    simpa only [J, IntegrableOn] using
      (levy_compensated_jump_integrable_nonneg X θ hθ)
  have hki (θ : ℝ) (hθ : 0 ≤ θ) :
      Integrable (K θ) (X.ν.restrict (Iio (0 : ℝ))) := by
    simpa only [K] using (hi θ hθ).div_const θ
  have hpoint (y : ℝ) (hy : y < 0) : K θ₁ y ≤ K θ₂ y := by
    have hs := exp_negative_secant_mono y θ₁ θ₂ hy hθ₁ hθ
    have heq (θ : ℝ) (hθ : 0 < θ) :
        K θ y =
          (Real.exp (θ * y) - 1) / θ -
            y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) := by
      dsimp [K, J]
      field_simp [ne_of_gt hθ]
    rw [heq θ₁ hθ₁, heq θ₂ hθ₂]
    exact sub_le_sub_right hs _
  have hae : ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))),
      K θ₁ y ≤ K θ₂ y := by
    filter_upwards [ae_restrict_mem (μ := X.ν) measurableSet_Iio] with y hy
    exact hpoint y hy
  have hint :
      (∫ y in Iio (0 : ℝ), K θ₁ y ∂X.ν) ≤
        ∫ y in Iio (0 : ℝ), K θ₂ y ∂X.ν :=
    integral_mono_ae (hki θ₁ hθ₁.le) (hki θ₂ hθ₂.le) hae
  have hrepr (θ : ℝ) (hθ : 0 < θ) :
      X.ψ θ / θ =
        X.c + (X.σ ^ 2 / 2) * θ +
          ∫ y in Iio (0 : ℝ), K θ y ∂X.ν := by
    have hdiv :
        (∫ y in Iio (0 : ℝ), K θ y ∂X.ν) =
          (∫ y in Iio (0 : ℝ), J θ y ∂X.ν) / θ := by
      simp only [K, integral_div]
    rw [hdiv]
    simp only [SpectrallyNegativeLevy.ψ, laplaceExponent, J]
    have hone : (1 : ℝ → ℝ) = (fun _ : ℝ => (1 : ℝ)) := rfl
    rw [hone]
    field_simp [ne_of_gt hθ]
  have hquad : (X.σ ^ 2 / 2) * θ₁ ≤ (X.σ ^ 2 / 2) * θ₂ :=
    mul_le_mul_of_nonneg_left hθ (div_nonneg (sq_nonneg _) (by norm_num))
  rw [hrepr θ₁ hθ₁, hrepr θ₂ hθ₂]
  exact add_le_add (add_le_add_right hquad X.c) hint

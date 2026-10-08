-- Prove2me | solution 1 for AvramDividend.Classical.psi_eventually_gt_of_boundedVariation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T07:09:10.65632+00:00
-- url     : https://prove2.me/submissions/b4c15c16-a5f7-42b3-8491-9ddb7b43bee3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_levy_small_negative_compensated_div_integrable
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable
import Theorems.Thm_AvramDividend_Classical_negative_compensated_real_integral_tendsto_finite
import Theorems.Thm_AvramDividend_Classical_negative_compensated_integral_mono
import Theorems.Thm_AvramDividend_Classical_psi_normalised_lower_bound_small


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by
  let s : Set ℝ := Ioo (-1 : ℝ) 0
  let μ : Measure ℝ := X.ν.restrict s
  let J : ℝ → ℝ := fun θ =>
    ∫ y : ℝ, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ
  let A : ℝ := ∫ y : ℝ, |y| ∂μ
  let B : ℝ := ∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν
  have hneg : ∀ᵐ y ∂μ, y < 0 := by
    dsimp [μ, s]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun y hy => hy.2)
  have hAneg : Integrable (fun y : ℝ => -y) μ := by
    simpa only [μ, s, IntegrableOn] using
      (bv_small_negative_first_moment_integrable X hBV)
  have hAint : Integrable (fun y : ℝ => |y|) μ := by
    simpa only [Real.norm_eq_abs, norm_neg, Real.norm_eq_abs] using hAneg.norm
  have hint : ∀ θ : ℝ, 0 < θ →
      Integrable (fun y : ℝ =>
        (Real.exp (θ * y) - 1 - θ * y) / θ) μ := by
    intro θ hθ
    simpa only [μ, s, IntegrableOn] using
      (levy_small_negative_compensated_div_integrable X θ hθ)
  have hJlim : Tendsto (fun n : ℕ => J ((n : ℝ) + 1))
      atTop (nhds A) := by
    have hlim :=
      negative_compensated_real_integral_tendsto_finite μ hneg hAint
        (fun n => hint ((n : ℝ) + 1) (by positivity))
    simpa only [J, A] using hlim
  have hJmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
      J θ₁ ≤ J θ₂ := by
    intro θ₁ θ₂ hθ₁ hθ
    have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ hθ
    exact negative_compensated_integral_mono μ θ₁ θ₂ hθ₁ hθ hneg
      (hint θ₁ hθ₁) (hint θ₂ hθ₂)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun _ => zero_le_one)
  have hAeq :
      A = -(∫ y in Ioo (-1 : ℝ) 0, y ∂X.ν) := by
    dsimp [A, μ, s]
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun y hy => by
      rw [abs_of_neg hy.2])
  have hd : 0 < X.c + A := by
    have hdrift := (bv_standing_drift_pos X hX hBV).1
    rw [hAeq]
    simpa only [SpectrallyNegativeLevy.drift, sub_eq_add_neg] using hdrift
  let d : ℝ := X.c + A
  have hd' : 0 < d := by simpa only [d] using hd
  have hδ : 0 < d / 4 := by positivity
  have hJev : ∀ᶠ n : ℕ in atTop,
      A - d / 4 < J ((n : ℝ) + 1) :=
    hJlim.eventually (Ioi_mem_nhds (sub_lt_self A hδ))
  have hq0 : Tendsto (fun n : ℕ => q / ((n : ℝ) + 1))
      atTop (nhds (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := q)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hB0 : Tendsto (fun n : ℕ => B / ((n : ℝ) + 1))
      atTop (nhds (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := B)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hqev : ∀ᶠ n : ℕ in atTop,
      q / ((n : ℝ) + 1) < d / 4 :=
    hq0.eventually (Iio_mem_nhds hδ)
  have hBev : ∀ᶠ n : ℕ in atTop,
      B / ((n : ℝ) + 1) < d / 4 :=
    hB0.eventually (Iio_mem_nhds hδ)
  have hev : ∀ᶠ n : ℕ in atTop,
      A - d / 4 < J ((n : ℝ) + 1) ∧
      q / ((n : ℝ) + 1) < d / 4 ∧
      B / ((n : ℝ) + 1) < d / 4 := by
    filter_upwards [hJev, hqev, hBev] with n hJn hqn hBn
    exact ⟨hJn, hqn, hBn⟩
  rcases hev.exists with ⟨N, hJN, hqN, hBN⟩
  refine ⟨(N : ℝ) + 1, (by positivity : 0 ≤ (N : ℝ) + 1), ?_⟩
  intro θ hθ
  have hNpos : 0 < (N : ℝ) + 1 := by positivity
  have hθpos : 0 < θ := lt_of_lt_of_le hNpos hθ
  have hJθ : J ((N : ℝ) + 1) ≤ J θ :=
    hJmono ((N : ℝ) + 1) θ hNpos hθ
  have hBθ : B / θ ≤ B / ((N : ℝ) + 1) := by
    apply (div_le_div_iff₀ hθpos hNpos).2
    exact mul_le_mul_of_nonneg_left hθ hB
  have hqθ : q / θ ≤ q / ((N : ℝ) + 1) := by
    apply (div_le_div_iff₀ hθpos hNpos).2
    exact mul_le_mul_of_nonneg_left hθ hq.le
  have hgap : q / θ < X.c + J θ - B / θ := by
    have hsmallq : q / θ < d / 4 := lt_of_le_of_lt hqθ hqN
    have hlower : d / 2 < X.c + J θ - B / θ := by
      dsimp [d] at hd' ⊢
      nlinarith
    have hquarter : d / 4 < d / 2 := by nlinarith
    exact lt_trans hsmallq (lt_trans hquarter hlower)
  have hlarge := levy_large_negative_jump_unit_integrable X
  have hlower :=
    psi_normalised_lower_bound_small X hBV.1 θ hθpos hlarge
  have hJeq :
      J θ =
        (∫ y in Ioo (-1 : ℝ) 0,
          (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) / θ := by
    dsimp [J, μ, s]
    exact integral_div θ
      (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y)
  have hnorm :
      X.c + J θ - B / θ ≤ X.ψ θ / θ := by
    simpa only [B, hJeq] using hlower
  have hqdiv : q / θ < X.ψ θ / θ :=
    lt_of_lt_of_le hgap hnorm
  exact (div_lt_div_iff_of_pos_right hθpos).mp hqdiv

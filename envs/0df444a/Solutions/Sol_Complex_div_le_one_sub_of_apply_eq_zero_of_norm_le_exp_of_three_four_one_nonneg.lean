-- Prove2me | solution 1 for Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e35e3cb4-35ff-5477-b8b2-e9f92f6652df

import Mathlib
import Theorems.Thm_Complex_neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg

set_option autoImplicit false

namespace R4ZFR

open Complex Metric

theorem landau (f : ℂ → ℂ) (s₀ : ℂ) (r M : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall s₀ r)) (h₀ : f s₀ ≠ 0)
    (hM : ∀ s ∈ Metric.closedBall s₀ r, ‖f s‖ ≤ Real.exp M * ‖f s₀‖)
    (hne : ∀ s ∈ Metric.closedBall s₀ (r / 2), s₀.re < s.re → f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall s₀ (r / 2) ∧ f ρ = 0) :
    -(deriv f s₀ / f s₀).re ≤ 8 * (M + 1) / r - ∑ ρ ∈ Z, ((s₀ - ρ)⁻¹).re :=
  Complex.neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re
    f s₀ r M hr hf h₀ hM hne Z hZ

theorem log_2048_le : Real.log 2048 ≤ 8 := by
  have h : (2048 : ℝ) = 2 ^ 11 := by norm_num
  rw [h, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  nlinarith

theorem M_bound (r 𝓛 : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (h𝓛 : 1 ≤ r * 𝓛) :
    Real.log (Real.exp (2 * 𝓛) / (r / (2048 * 𝓛)) ^ 2) + 1 ≤ 22 * 𝓛 := by
  have h𝓛1 : 1 ≤ 𝓛 := by nlinarith
  have h𝓛0 : 0 < 𝓛 := by linarith
  have hδ0 : 0 < r / (2048 * 𝓛) := by positivity
  rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow]

  have hlogδ : Real.log (r / (2048 * 𝓛)) = Real.log r - Real.log 2048 - Real.log 𝓛 := by
    rw [Real.log_div hr.ne' (by positivity), Real.log_mul (by norm_num) h𝓛0.ne']
    ring
  have hlog𝓛 : Real.log 𝓛 ≤ 𝓛 - 1 := Real.log_le_sub_one_of_pos h𝓛0
  have hlogr : -Real.log r ≤ 𝓛 - 1 := by
    have h1 : Real.log r⁻¹ ≤ r⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
    rw [Real.log_inv] at h1
    have h2 : r⁻¹ ≤ 𝓛 := by
      rw [inv_le_iff_one_le_mul₀ hr, mul_comm]
      exact h𝓛
    linarith
  have h2048 := log_2048_le
  rw [hlogδ]
  push_cast
  nlinarith

theorem main (F₁ F₂ : ℂ → ℂ) (β γ r 𝓛 C₀ : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (h𝓛 : 1 ≤ r * 𝓛) (hC₀ : 0 ≤ C₀) (hC₀𝓛 : C₀ ≤ 𝓛)
    (hρ : F₁ ((β : ℂ) + γ * I) = 0)
    (h1nz : ∀ s : ℂ, 1 < s.re → F₁ s ≠ 0)
    (h2nz : ∀ s : ℂ, 1 < s.re → F₂ s ≠ 0)
    (h1an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₁ (Metric.closedBall ((σ : ℂ) + γ * I) r))
    (h2an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₂ (Metric.closedBall ((σ : ℂ) + 2 * γ * I) r))
    (h1up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + γ * I) r, ‖F₁ s‖ ≤ Real.exp 𝓛)
    (h2up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + 2 * γ * I) r, ‖F₂ s‖ ≤ Real.exp 𝓛)
    (h1lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₁ ((σ : ℂ) + γ * I)‖)
    (h2lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₂ ((σ : ℂ) + 2 * γ * I)‖)
    (h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      0 ≤ 3 * (1 / (σ - 1) + C₀)
        + 4 * (-(deriv F₁ ((σ : ℂ) + γ * I) / F₁ ((σ : ℂ) + γ * I))).re
        + (-(deriv F₂ ((σ : ℂ) + 2 * γ * I) / F₂ ((σ : ℂ) + 2 * γ * I))).re) :
    r / (20000 * 𝓛) ≤ 1 - β := by

  have h𝓛1 : 1 ≤ 𝓛 := by nlinarith
  have h𝓛0 : 0 < 𝓛 := by linarith

  have hβ : β ≤ 1 := by
    by_contra h
    push Not at h
    exact h1nz ((β : ℂ) + γ * I) (by simpa using h) hρ

  set δ : ℝ := r / (2048 * 𝓛) with hδ_def
  have hδ0 : 0 < δ := by positivity
  have hδr : δ ≤ r / 2048 := by
    rw [hδ_def, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set σ : ℝ := 1 + δ with hσ_def
  have hσ1 : 1 < σ := by linarith
  have hσr : σ ≤ 1 + r := by linarith

  have hgoal_small : r / (20000 * 𝓛) ≤ r / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

  by_cases hfar : r / 2 < σ - β
  ·
    have : r / 4 ≤ 1 - β := by
      have h1 : σ - β = 1 - β + δ := by rw [hσ_def]; ring
      nlinarith
    linarith
  push Not at hfar

  set M : ℝ := Real.log (Real.exp (2 * 𝓛) / δ ^ 2) with hM_def
  have hMexp : Real.exp M = Real.exp (2 * 𝓛) / δ ^ 2 := by
    rw [hM_def, Real.exp_log (by positivity)]
  have hM1 : M + 1 ≤ 22 * 𝓛 := by
    have := M_bound r 𝓛 hr hr1 h𝓛
    simpa [hM_def, hδ_def] using this

  have hlo₁ := h1lo σ hσ1 hσr
  have hlo₂ := h2lo σ hσ1 hσr
  have h3 := h341 σ hσ1 hσr
  have hσδ : σ - 1 = δ := by rw [hσ_def]; ring
  rw [hσδ] at hlo₁ hlo₂ h3
  simp only [Complex.neg_re] at h3

  set s₁ : ℂ := (σ : ℂ) + γ * I with hs₁_def
  set s₂ : ℂ := (σ : ℂ) + 2 * γ * I with hs₂_def
  have hs₁re : s₁.re = σ := by simp [hs₁_def]
  have hs₂re : s₂.re = σ := by simp [hs₂_def]
  have hpos : 0 < δ ^ 2 * Real.exp (-𝓛) := by positivity
  have hF₁0 : F₁ s₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hlo₁; linarith
  have hF₂0 : F₂ s₂ ≠ 0 := by
    intro h; rw [h, norm_zero] at hlo₂; linarith

  have hratio : ∀ (x y : ℝ), x ≤ Real.exp 𝓛 → δ ^ 2 * Real.exp (-𝓛) ≤ y →
      x ≤ Real.exp M * y := by
    intro x y hx hy
    rw [hMexp]
    have hδ2 : 0 < δ ^ 2 := by positivity
    calc x ≤ Real.exp 𝓛 := hx
      _ = Real.exp (2 * 𝓛) / δ ^ 2 * (δ ^ 2 * Real.exp (-𝓛)) := by
          rw [show (2 : ℝ) * 𝓛 = 𝓛 + 𝓛 by ring, Real.exp_add, Real.exp_neg]
          field_simp
      _ ≤ Real.exp (2 * 𝓛) / δ ^ 2 * y :=
          mul_le_mul_of_nonneg_left hy (by positivity)
  have hM₁ : ∀ s ∈ Metric.closedBall s₁ r, ‖F₁ s‖ ≤ Real.exp M * ‖F₁ s₁‖ :=
    fun s hs => hratio _ _ (h1up σ hσ1 hσr s hs) hlo₁
  have hM₂ : ∀ s ∈ Metric.closedBall s₂ r, ‖F₂ s‖ ≤ Real.exp M * ‖F₂ s₂‖ :=
    fun s hs => hratio _ _ (h2up σ hσ1 hσr s hs) hlo₂
  have hne₁ : ∀ s ∈ Metric.closedBall s₁ (r / 2), s₁.re < s.re → F₁ s ≠ 0 :=
    fun s _ hs => h1nz s (by rw [hs₁re] at hs; linarith)
  have hne₂ : ∀ s ∈ Metric.closedBall s₂ (r / 2), s₂.re < s.re → F₂ s ≠ 0 :=
    fun s _ hs => h2nz s (by rw [hs₂re] at hs; linarith)

  set ρ : ℂ := (β : ℂ) + γ * I with hρ_def
  have hsub : s₁ - ρ = ((σ - β : ℝ) : ℂ) := by
    rw [hs₁_def, hρ_def]; push_cast; ring
  have hσβ : 0 < σ - β := by linarith
  have hρmem : ρ ∈ Metric.closedBall s₁ (r / 2) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, ← neg_sub, norm_neg, hsub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσβ]
    exact hfar

  have hL₁ := landau F₁ s₁ r M hr (h1an σ hσ1 hσr) hF₁0 hM₁ hne₁ {ρ}
    (fun ρ' hρ' => by
      rw [Finset.mem_singleton] at hρ'
      subst hρ'
      exact ⟨hρmem, hρ⟩)
  have hL₂ := landau F₂ s₂ r M hr (h2an σ hσ1 hσr) hF₂0 hM₂ hne₂ ∅ (by simp)
  rw [Finset.sum_singleton, hsub, ← Complex.ofReal_inv, Complex.ofReal_re] at hL₁
  rw [Finset.sum_empty, sub_zero] at hL₂

  set X : ℝ := (M + 1) / r with hX_def
  set a : ℝ := (deriv F₁ s₁ / F₁ s₁).re with ha_def
  set b : ℝ := (deriv F₂ s₂ / F₂ s₂).re with hb_def
  have e1 : 8 * (M + 1) / r = 8 * X := by rw [hX_def]; ring
  rw [e1] at hL₁ hL₂
  have e3 : 3 * (1 / δ + C₀) = 3 / δ + 3 * C₀ := by ring
  rw [e3] at h3
  have hkey : 4 * (σ - β)⁻¹ ≤ 3 / δ + 3 * C₀ + 40 * X := by
    linarith

  have hM1r : X ≤ 22 * 𝓛 / r := by
    rw [hX_def]; exact div_le_div_of_nonneg_right hM1 hr.le
  have h3δ : 3 / δ = 3 * 2048 * 𝓛 / r := by
    rw [hδ_def]; field_simp
  have hC₀r : C₀ ≤ 𝓛 / r := by
    rw [le_div_iff₀ hr]
    nlinarith
  have hrhs : 3 / δ + 3 * C₀ + 40 * X ≤ 7027 * 𝓛 / r := by
    rw [h3δ]
    have : 3 * 2048 * 𝓛 / r + 3 * (𝓛 / r) + 40 * (22 * 𝓛 / r) = 7027 * 𝓛 / r := by ring
    linarith
  have h4 : 4 * (σ - β)⁻¹ ≤ 7027 * 𝓛 / r := hkey.trans hrhs

  have hσβ' : 4 * r / (7027 * 𝓛) ≤ σ - β := by
    have h5 : 4 / (σ - β) ≤ 7027 * 𝓛 / r := by rwa [div_eq_mul_inv]
    rw [div_le_div_iff₀ hσβ (by positivity)] at h5
    rw [div_le_iff₀ (by positivity)]
    linarith

  have h1β : 1 - β = σ - β - δ := by rw [hσ_def]; ring
  rw [h1β, hδ_def]
  have hq : (1 : ℝ) / 20000 ≤ 4 / 7027 - 1 / 2048 := by norm_num
  have h7 : r / (20000 * 𝓛) ≤ 4 * r / (7027 * 𝓛) - r / (2048 * 𝓛) := by
    have hr𝓛 : 0 ≤ r / 𝓛 := by positivity
    calc r / (20000 * 𝓛) = r / 𝓛 * (1 / 20000) := by ring
      _ ≤ r / 𝓛 * (4 / 7027 - 1 / 2048) := mul_le_mul_of_nonneg_left hq hr𝓛
      _ = 4 * r / (7027 * 𝓛) - r / (2048 * 𝓛) := by ring
  linarith

end R4ZFR

theorem solution
    (F₁ F₂ : ℂ → ℂ) (β γ r 𝓛 C₀ : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (h𝓛 : 1 ≤ r * 𝓛) (hC₀ : 0 ≤ C₀) (hC₀𝓛 : C₀ ≤ 𝓛)
    (hρ : F₁ ((β : ℂ) + γ * Complex.I) = 0)
    (h1nz : ∀ s : ℂ, 1 < s.re → F₁ s ≠ 0)
    (h2nz : ∀ s : ℂ, 1 < s.re → F₂ s ≠ 0)
    (h1an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₁ (Metric.closedBall ((σ : ℂ) + γ * Complex.I) r))
    (h2an : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      AnalyticOnNhd ℂ F₂ (Metric.closedBall ((σ : ℂ) + 2 * γ * Complex.I) r))
    (h1up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + γ * Complex.I) r, ‖F₁ s‖ ≤ Real.exp 𝓛)
    (h2up : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      ∀ s ∈ Metric.closedBall ((σ : ℂ) + 2 * γ * Complex.I) r, ‖F₂ s‖ ≤ Real.exp 𝓛)
    (h1lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₁ ((σ : ℂ) + γ * Complex.I)‖)
    (h2lo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖F₂ ((σ : ℂ) + 2 * γ * Complex.I)‖)
    (h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
      0 ≤ 3 * (1 / (σ - 1) + C₀)
        + 4 * (-(deriv F₁ ((σ : ℂ) + γ * Complex.I) / F₁ ((σ : ℂ) + γ * Complex.I))).re
        + (-(deriv F₂ ((σ : ℂ) + 2 * γ * Complex.I) / F₂ ((σ : ℂ) + 2 * γ * Complex.I))).re) :
    r / (20000 * 𝓛) ≤ 1 - β :=
  R4ZFR.main F₁ F₂ β γ r 𝓛 C₀ hr hr1 h𝓛 hC₀ hC₀𝓛 hρ h1nz h2nz h1an h2an h1up h2up h1lo h2lo h341

end S_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
end P2MW
export P2MW.S_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg (solution)

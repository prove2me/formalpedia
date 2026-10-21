-- Prove2me | solution 1 for CondatPD.FB.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:20:47.657619+00:00
-- url     : https://prove2.me/submissions/ca2fc1c7-92e0-4682-b40d-408e50e5e76a

import Mathlib
import Definitions.Def_CondatPD_FB_Setting

set_option autoImplicit false

section CdSec
open scoped InnerProductSpace
namespace Cd
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem avg_eq {α : ℝ} (hα : 0 < α) (q u n : K) (hq : q = α • n + (1 - α) • u) :
    ‖q‖ ^ 2 + ((1 - α) / α) * ‖u - q‖ ^ 2 = α * ‖n‖ ^ 2 + (1 - α) * ‖u‖ ^ 2 := by
  have e : u - q = α • (u - n) := by rw [hq]; module
  have h1 : ‖q‖ ^ 2 = α ^ 2 * ‖n‖ ^ 2 + 2 * (α * (1 - α)) * ⟪n, u⟫_ℝ + (1 - α) ^ 2 * ‖u‖ ^ 2 := by
    rw [hq, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  have h2 : ‖u - q‖ ^ 2 = α ^ 2 * (‖u‖ ^ 2 - 2 * ⟪n, u⟫_ℝ + ‖n‖ ^ 2) := by
    rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sub_sq_real, real_inner_comm]
  rw [h1, h2]
  field_simp
  ring

theorem avg_ineq {α : ℝ} (h0 : 0 < α) (h1 : α ≤ 1) {T N : K → K}
    (hN : ∀ x y, ‖N x - N y‖ ≤ ‖x - y‖) (hT : ∀ x, T x = α • N x + (1 - α) • x) (x y : K) :
    ‖T x - T y‖ ^ 2 + ((1 - α) / α) * ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have e1 : T x - T y = α • (N x - N y) + (1 - α) • (x - y) := by rw [hT x, hT y]; module
  have e2 : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by abel
  rw [e2]
  have := avg_eq h0 (T x - T y) (x - y) (N x - N y) e1
  rw [this]
  have hh : ‖N x - N y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hN x y) 2
  nlinarith

end Cd
end CdSec

open CondatPD.FB

theorem solution {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (α₁ α₂ : ℝ) (T₁ T₂ : K → K)
    (hα₁ : 0 < α₁ ∧ α₁ < 1) (hα₂ : 0 < α₂ ∧ α₂ ≤ 1)
    (hT₁ : IsAvg α₁ T₁) (hT₂ : IsAvg α₂ T₂) :
    IsAvg ((α₁ + α₂ - 2 * α₁ * α₂) / (1 - α₁ * α₂)) (T₁ ∘ T₂) := by
  obtain ⟨h1p, h1l⟩ := hα₁
  obtain ⟨h2p, h2l⟩ := hα₂
  obtain ⟨-, -, N1, hN1, hT1⟩ := hT₁
  obtain ⟨-, -, N2, hN2, hT2⟩ := hT₂
  have hD : 0 < 1 - α₁ * α₂ := by nlinarith
  have hP : 0 < (1 - α₁) * α₂ := mul_pos (by linarith) h2p
  have hQ : 0 ≤ (1 - α₂) * α₁ := mul_nonneg (by linarith) h1p.le
  have hnum : 0 < α₁ + α₂ - 2 * α₁ * α₂ := by nlinarith
  obtain ⟨α, hα⟩ : ∃ α, α = (α₁ + α₂ - 2 * α₁ * α₂) / (1 - α₁ * α₂) := ⟨_, rfl⟩
  rw [← hα]
  have hαpos : 0 < α := by rw [hα]; exact div_pos hnum hD
  have hαle : α ≤ 1 := by
    rw [hα, div_le_one hD]; nlinarith
  have hα1 : 1 - α = (1 - α₁) * (1 - α₂) / (1 - α₁ * α₂) := by
    rw [hα]; field_simp; ring
  refine ⟨hαpos, hαle, fun x => (1 / α) • ((T₁ ∘ T₂) x - (1 - α) • x), ?_, ?_⟩
  · intro x y
    set u := x - y with hu
    set p := T₂ x - T₂ y with hp
    set q := (T₁ ∘ T₂) x - (T₁ ∘ T₂) y with hq
    have hA := Cd.avg_ineq h2p h2l hN2 hT2 x y
    have hB := Cd.avg_ineq h1p h1l.le hN1 hT1 (T₂ x) (T₂ y)
    have hsub : ‖u - q‖ ≤ ‖u - p‖ + ‖p - q‖ := by
      calc ‖u - q‖ = ‖(u - p) + (p - q)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hu2 : ‖u - q‖ ^ 2 ≤ (‖u - p‖ + ‖p - q‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsub 2
    have hA' : ‖p‖ ^ 2 + ((1 - α₂) / α₂) * ‖u - p‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have : (x - T₂ x) - (y - T₂ y) = u - p := by simp only [hu, hp]; abel
      rw [this] at hA; exact hA
    have hB' : ‖q‖ ^ 2 + ((1 - α₁) / α₁) * ‖p - q‖ ^ 2 ≤ ‖p‖ ^ 2 := by
      have : (T₂ x - T₁ (T₂ x)) - (T₂ y - T₁ (T₂ y)) = p - q := by simp only [hp, hq, Function.comp]; abel
      rw [this] at hB; exact hB
    -- Cauchy-type estimate
    have hcs : ((1 - α) / α) * (‖u - p‖ + ‖p - q‖) ^ 2
        ≤ ((1 - α₁) / α₁) * ‖p - q‖ ^ 2 + ((1 - α₂) / α₂) * ‖u - p‖ ^ 2 := by
      obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (1 - α₁) * α₂ + (1 - α₂) * α₁ := ⟨_, rfl⟩
      have hDne : D ≠ 0 := by rw [hDdef]; positivity
      have hDpos : 0 < D := by rw [hDdef]; positivity
      have hc : (1 - α) / α = (1 - α₁) * (1 - α₂) / D := by
        rw [hα1, hα, hDdef, div_div_div_cancel_right₀ hD.ne']
        congr 1; ring
      have key : ((1 - α₁) / α₁) * ‖p - q‖ ^ 2 + ((1 - α₂) / α₂) * ‖u - p‖ ^ 2
          - ((1 - α) / α) * (‖u - p‖ + ‖p - q‖) ^ 2
          = (((1 - α₁) * α₂) * ‖p - q‖ - ((1 - α₂) * α₁) * ‖u - p‖) ^ 2
            / (α₁ * α₂ * D) := by
        rw [hc]
        field_simp
        rw [hDdef]
        ring
      have : 0 ≤ (((1 - α₁) * α₂) * ‖p - q‖ - ((1 - α₂) * α₁) * ‖u - p‖) ^ 2
            / (α₁ * α₂ * D) := by positivity
      linarith
    have hc0 : 0 ≤ (1 - α) / α := div_nonneg (by linarith) hαpos.le
    have hfin : ‖q‖ ^ 2 + ((1 - α) / α) * ‖u - q‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hu2 hc0
      linarith
    -- convert to nonexpansiveness of N
    set n : K := (1 / α) • (q - (1 - α) • u) with hn
    have hqn : q = α • n + (1 - α) • u := by
      rw [hn, smul_smul, mul_one_div_cancel hαpos.ne', one_smul]; abel
    have hE := Cd.avg_eq hαpos q u n hqn
    have hnn : ‖n‖ ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith
    have hnorm : ‖n‖ ≤ ‖u‖ := by
      by_contra h
      push_neg at h
      have := pow_lt_pow_left₀ h (norm_nonneg _) (by norm_num : (2:ℕ) ≠ 0)
      linarith
    have e : (1 / α) • ((T₁ ∘ T₂) x - (1 - α) • x) - (1 / α) • ((T₁ ∘ T₂) y - (1 - α) • y) = n := by
      rw [hn, ← smul_sub]
      congr 1
      simp only [hq, hu]
      module
    show ‖(1 / α) • ((T₁ ∘ T₂) x - (1 - α) • x) - (1 / α) • ((T₁ ∘ T₂) y - (1 - α) • y)‖ ≤ ‖x - y‖
    rw [e]; exact hnorm
  · intro x
    rw [smul_smul, mul_one_div_cancel hαpos.ne', one_smul]
    abel

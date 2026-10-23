-- Prove2me | solution 1 for CustomerVoice.OLearn.ic_case_low
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:34:21.746866+00:00
-- url     : https://prove2.me/submissions/3cc90b6a-8d1e-46ce-ba74-abb561d1da18

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

open CustomerVoice.OLearn in
theorem solution (M : Model) (hM : M.Standing) (hγ : M.γ ≤ M.s / M.k) :
    (M.ICH' ↔ M.θH / M.θL ≥ M.LambdaH1) ∧ (M.ICL' ↔ M.θH / M.θL ≥ M.LambdaL) := by
  obtain ⟨hL, hLH, -, -, hg0, hg1, hk, hs⟩ := hM
  have hsk : M.γ * M.k ≤ M.s := by rwa [le_div_iff₀ hk] at hγ
  have hD : 0 < M.s + M.γ * M.k := by positivity
  have hq : ∀ θ : ℝ, 0 < θ → M.qStar θ = M.γ * θ / (M.s + M.γ * M.k) := by
    intro θ hθ
    unfold Model.qStar
    apply min_eq_left
    rw [div_le_div_iff₀ hD (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsk hθ.le, mul_pos hg0 hθ]
  have hH0 : 0 < M.θH := by linarith
  have hqH : M.qO .H = M.γ * M.θH / (M.s + M.γ * M.k) := hq _ (by unfold Model.θ; linarith)
  have hqL : M.qO .L = M.γ * M.θL / (M.s + M.γ * M.k) := hq _ (by unfold Model.θ; linarith)
  set D := M.s + M.γ * M.k with hDdef
  have hratio : ∀ c : ℝ, (M.θH / M.θL ≥ c ↔ c * M.θL ≤ M.θH) := by
    intro c; rw [ge_iff_le, le_div_iff₀ hL]
  unfold Model.ICH' Model.ICL' Model.mu Model.LambdaH1 Model.LambdaL
  rw [hqH, hqL, hratio, hratio]
  constructor
  · -- IC'_H
    have e1 : max (M.θH * (M.γ * M.θL / D) - M.θL * (M.γ * M.θL / D)) 0
        = M.θH * (M.γ * M.θL / D) - M.θL * (M.γ * M.θL / D) := by
      apply max_eq_left
      have : 0 ≤ (M.θH - M.θL) * (M.γ * M.θL / D) := by
        apply mul_nonneg <;> [linarith; positivity]
      linarith
    have e2 : max (M.θH * (M.γ * M.θL / D) - M.k * (M.γ * M.θL / D) ^ 2) 0
        = M.θH * (M.γ * M.θL / D) - M.k * (M.γ * M.θL / D) ^ 2 := by
      apply max_eq_left
      have : M.θH * (M.γ * M.θL / D) - M.k * (M.γ * M.θL / D) ^ 2
          = M.γ * M.θL * (D * M.θH - M.k * M.γ * M.θL) / D ^ 2 := by field_simp; try ring
      rw [this]
      exact div_nonneg (mul_nonneg (by positivity) (by nlinarith [mul_pos hg0 hk, mul_pos hs hL])) (by positivity)
    have e3 : max (M.θH * (M.γ * M.θH / D) - M.θH * (M.γ * M.θH / D)) 0 = 0 := by simp
    have e4 : max (M.θH * (M.γ * M.θH / D) - M.k * (M.γ * M.θH / D) ^ 2) 0
        = M.γ * M.s * M.θH ^ 2 / D ^ 2 := by
      have : M.θH * (M.γ * M.θH / D) - M.k * (M.γ * M.θH / D) ^ 2 = M.γ * M.s * M.θH ^ 2 / D ^ 2 := by
        rw [hDdef]; field_simp; ring
      rw [this]; apply max_eq_left; positivity
    rw [e1, e2, e3, e4]
    have key : M.γ * 0 + (1 - M.γ) * (M.γ * M.s * M.θH ^ 2 / D ^ 2) -
        (M.γ * (M.θH * (M.γ * M.θL / D) - M.θL * (M.γ * M.θL / D)) +
        (1 - M.γ) * (M.θH * (M.γ * M.θL / D) - M.k * (M.γ * M.θL / D) ^ 2)) =
        M.γ / D ^ 2 * ((M.θH - M.θL) * ((1 - M.γ) * M.s * M.θH - M.γ * (M.s + M.k) * M.θL)) := by
      rw [hDdef]; field_simp; ring
    have hc : 0 < M.γ / D ^ 2 := by positivity
    have h1 : 0 < M.θH - M.θL := by linarith
    have h1g : 0 < (1 - M.γ) * M.s := by nlinarith
    have hA : M.γ * (M.s + M.k) / ((1 - M.γ) * M.s) * M.θL ≤ M.θH ↔
        M.γ * (M.s + M.k) * M.θL ≤ M.θH * ((1 - M.γ) * M.s) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1g]
    rw [← sub_nonneg, key, hA]
    constructor
    · intro h
      have h2 := nonneg_of_mul_nonneg_right (by linarith [h] : 0 ≤ M.γ / D ^ 2 * ((M.θH - M.θL) * ((1 - M.γ) * M.s * M.θH - M.γ * (M.s + M.k) * M.θL))) hc
      have h3 := nonneg_of_mul_nonneg_right (by linarith [h2] : 0 ≤ (M.θH - M.θL) * ((1 - M.γ) * M.s * M.θH - M.γ * (M.s + M.k) * M.θL)) h1
      nlinarith
    · intro h
      apply mul_nonneg hc.le
      apply mul_nonneg h1.le
      nlinarith
  · -- IC'_L
    have e3 : max (M.θL * (M.γ * M.θH / D) - M.θH * (M.γ * M.θH / D)) 0 = 0 := by
      apply max_eq_right
      have : 0 ≤ (M.θH - M.θL) * (M.γ * M.θH / D) := by
        apply mul_nonneg <;> [linarith; positivity]
      linarith
    have e5 : max (M.θL * (M.γ * M.θL / D) - M.θL * (M.γ * M.θL / D)) 0 = 0 := by simp
    have e4 : max (M.θL * (M.γ * M.θL / D) - M.k * (M.γ * M.θL / D) ^ 2) 0
        = M.γ * M.s * M.θL ^ 2 / D ^ 2 := by
      have : M.θL * (M.γ * M.θL / D) - M.k * (M.γ * M.θL / D) ^ 2 = M.γ * M.s * M.θL ^ 2 / D ^ 2 := by
        rw [hDdef]; field_simp; ring
      rw [this]; apply max_eq_left; positivity
    have e6 : M.θL * (M.γ * M.θH / D) - M.k * (M.γ * M.θH / D) ^ 2
        = M.γ * M.s * M.θL ^ 2 / D ^ 2 -
          M.γ / D ^ 2 * ((M.θH - M.θL) * (M.k * M.γ * M.θH - M.s * M.θL)) := by
      rw [hDdef]; field_simp; ring
    rw [e3, e5, e4, e6]
    have hc : 0 < M.γ / D ^ 2 := by positivity
    have h1 : 0 < M.θH - M.θL := by linarith
    have hpos : 0 < M.γ * M.s * M.θL ^ 2 / D ^ 2 := by positivity
    have h1g : 0 < M.γ * M.k := by positivity
    have hA : M.s / (M.γ * M.k) * M.θL ≤ M.θH ↔ M.s * M.θL ≤ M.θH * (M.γ * M.k) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1g]
    rw [hA]
    have hg1' : 0 < 1 - M.γ := by linarith
    generalize hX : M.γ * M.s * M.θL ^ 2 / D ^ 2 = X at hpos ⊢
    have hY : 0 ≤ M.γ / D ^ 2 * ((M.θH - M.θL) * (M.k * M.γ * M.θH - M.s * M.θL)) ↔
        M.s * M.θL ≤ M.θH * (M.γ * M.k) := by
      constructor
      · intro h
        have h5 := nonneg_of_mul_nonneg_right (nonneg_of_mul_nonneg_right h hc) h1
        nlinarith
      · intro h
        apply mul_nonneg hc.le; apply mul_nonneg h1.le; nlinarith
    rw [← hY]
    generalize M.γ / D ^ 2 * ((M.θH - M.θL) * (M.k * M.γ * M.θH - M.s * M.θL)) = Y
    rw [mul_zero, zero_add, zero_add, mul_le_mul_iff_right₀ hg1', max_le_iff]
    constructor
    · rintro ⟨h, -⟩; linarith
    · intro h; exact ⟨by linarith, hpos.le⟩

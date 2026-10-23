-- Prove2me | solution 1 for CustomerVoice.OLearn.ic_case_high
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:31:08.386685+00:00
-- url     : https://prove2.me/submissions/ecc9b4df-8642-482f-a7ef-18951e93d120

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

open CustomerVoice.OLearn in
theorem solution (M : Model) (hM : M.Standing) (hγ : M.s / M.k ≤ M.γ) :
    (M.ICH' ↔ M.θH / M.θL ≥ M.LambdaH2) ∧
    M.mu (M.qO .H) M.θL M.θH < M.mu (M.qO .L) M.θL M.θL := by
  obtain ⟨hL, hLH, -, -, hg0, hg1, hk, hs⟩ := hM
  have hsk : M.s ≤ M.γ * M.k := by rwa [div_le_iff₀ hk] at hγ
  have hq : ∀ θ : ℝ, 0 < θ → M.qStar θ = θ / (2 * M.k) := by
    intro θ hθ
    unfold Model.qStar
    apply min_eq_right
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsk hθ.le]
  have hqH : M.qO .H = M.θH / (2 * M.k) := hq _ (by unfold Model.θ; linarith)
  have hqL : M.qO .L = M.θL / (2 * M.k) := hq _ (by unfold Model.θ; linarith)
  have hH0 : 0 < M.θH := by linarith
  set r := M.θH / M.θL with hr
  have hθH : M.θH = r * M.θL := by rw [hr]; field_simp
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hL]; linarith
  rw [hqH, hqL]
  unfold Model.ICH' Model.mu Model.LambdaH2
  rw [hqH, hqL]
  constructor
  · rw [ge_iff_le, div_le_iff₀ (by linarith)]
    have e1 : max (M.θH * (M.θL / (2 * M.k)) - M.θL * (M.θL / (2 * M.k))) 0
        = M.θH * (M.θL / (2 * M.k)) - M.θL * (M.θL / (2 * M.k)) := by
      apply max_eq_left
      have : 0 ≤ (M.θH - M.θL) * (M.θL / (2 * M.k)) := by
        apply mul_nonneg <;> [linarith; positivity]
      linarith
    have e2 : max (M.θH * (M.θL / (2 * M.k)) - M.k * (M.θL / (2 * M.k)) ^ 2) 0
        = M.θH * (M.θL / (2 * M.k)) - M.k * (M.θL / (2 * M.k)) ^ 2 := by
      apply max_eq_left
      have : M.θH * (M.θL / (2 * M.k)) - M.k * (M.θL / (2 * M.k)) ^ 2
          = M.θL * (2 * M.θH - M.θL) / (4 * M.k) := by field_simp; ring
      rw [this]; apply div_nonneg <;> nlinarith
    have e3 : max (M.θH * (M.θH / (2 * M.k)) - M.θH * (M.θH / (2 * M.k))) 0 = 0 := by simp
    have e4 : max (M.θH * (M.θH / (2 * M.k)) - M.k * (M.θH / (2 * M.k)) ^ 2) 0
        = M.θH ^ 2 / (4 * M.k) := by
      have : M.θH * (M.θH / (2 * M.k)) - M.k * (M.θH / (2 * M.k)) ^ 2 = M.θH ^ 2 / (4 * M.k) := by
        field_simp; ring
      rw [this]; apply max_eq_left; positivity
    rw [e1, e2, e3, e4]
    have key : M.γ * (M.θH * (M.θL / (2 * M.k)) - M.θL * (M.θL / (2 * M.k))) +
        (1 - M.γ) * (M.θH * (M.θL / (2 * M.k)) - M.k * (M.θL / (2 * M.k)) ^ 2) ≤
        M.γ * 0 + (1 - M.γ) * (M.θH ^ 2 / (4 * M.k)) ↔
        2 * M.γ * (r - 1) ≤ (1 - M.γ) * (r - 1) ^ 2 := by
      rw [hθH]
      constructor
      · intro h
        field_simp at h
        have h2 : M.θL ^ 2 * (M.γ * 2 * (r - 1) + (1 - M.γ) * (r * 2 - 1)) ≤
            M.θL ^ 2 * (r ^ 2 * (1 - M.γ)) := by nlinarith
        have h3 := le_of_mul_le_mul_left h2 (by positivity)
        nlinarith
      · intro h
        have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ M.θL ^ 2 / (4 * M.k) by positivity)
        field_simp at h' ⊢; nlinarith
    rw [key]
    constructor
    · intro h
      have : 2 * M.γ ≤ (1 - M.γ) * (r - 1) := by
        by_contra hc; push Not at hc
        nlinarith
      nlinarith
    · intro h
      have : 2 * M.γ ≤ (1 - M.γ) * (r - 1) := by nlinarith
      nlinarith
  · have e3 : max (M.θL * (M.θH / (2 * M.k)) - M.θH * (M.θH / (2 * M.k))) 0 = 0 := by
      apply max_eq_right
      have : 0 ≤ (M.θH - M.θL) * (M.θH / (2 * M.k)) := by
        apply mul_nonneg <;> [linarith; positivity]
      linarith
    have e5 : max (M.θL * (M.θL / (2 * M.k)) - M.θL * (M.θL / (2 * M.k))) 0 = 0 := by simp
    have e4 : max (M.θL * (M.θL / (2 * M.k)) - M.k * (M.θL / (2 * M.k)) ^ 2) 0
        = M.θL ^ 2 / (4 * M.k) := by
      have : M.θL * (M.θL / (2 * M.k)) - M.k * (M.θL / (2 * M.k)) ^ 2 = M.θL ^ 2 / (4 * M.k) := by
        field_simp; ring
      rw [this]; apply max_eq_left; positivity
    rw [e3, e5, e4]
    have hlt : max (M.θL * (M.θH / (2 * M.k)) - M.k * (M.θH / (2 * M.k)) ^ 2) 0 < M.θL ^ 2 / (4 * M.k) := by
      apply max_lt
      · have : M.θL * (M.θH / (2 * M.k)) - M.k * (M.θH / (2 * M.k)) ^ 2
            = (2 * M.θL * M.θH - M.θH ^ 2) / (4 * M.k) := by field_simp; ring
        rw [this, div_lt_div_iff_of_pos_right (by positivity)]
        nlinarith
      · positivity
    nlinarith

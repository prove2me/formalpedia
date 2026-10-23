-- Prove2me | solution 1 for CustomerVoice.ONoOther.high_mimics_low
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:40:23.571997+00:00
-- url     : https://prove2.me/submissions/dc02de20-8f8f-42e3-a1e9-ffb781aa3c44

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting
import Theorems.Thm_CustomerVoice_ONoOther_low_request_first_best

namespace CustomerVoice.ONoOther.HMLProof
open CustomerVoice.ONoOther CustomerVoice.ALearn

lemma accepts_le (M : Model) (hM : M.Standing) {θh q : ℝ} (hθ : 0 ≤ θh) (hq : 0 ≤ q)
    (h : M.accepts θh q) : q ≤ M.γ * θh / (M.s + M.γ * M.k) := by
  obtain ⟨hL, hLH, hα0, hα1, hγ0, hγ1, hk, hs⟩ := hM
  have hD : 0 < M.s + M.γ * M.k := by positivity
  rw [le_div_iff₀ hD]
  unfold Model.accepts at h
  rcases hq.lt_or_eq with hq | hq
  · by_contra hn
    push Not at hn
    nlinarith [mul_pos hq (sub_pos.mpr hn)]
  · subst hq
    have : 0 ≤ M.γ * θh := by nlinarith
    nlinarith

lemma accepts_of_le (M : Model) (hM : M.Standing) {θh q : ℝ} (hq : 0 ≤ q)
    (h : q ≤ M.γ * θh / (M.s + M.γ * M.k)) : M.accepts θh q := by
  obtain ⟨hL, hLH, hα0, hα1, hγ0, hγ1, hk, hs⟩ := hM
  have hD : 0 < M.s + M.γ * M.k := by positivity
  rw [le_div_iff₀ hD] at h
  unfold Model.accepts
  nlinarith [mul_nonneg hq (sub_nonneg.mpr h)]

lemma θH_eq (M : Model) : M.θ .H = M.θH := rfl
lemma θL_eq (M : Model) : M.θ .L = M.θL := rfl

lemma theta_bounds (M : Model) (hM : M.Standing) (t : BType) :
    M.θL ≤ M.θ t ∧ M.θ t ≤ M.θH := by
  obtain ⟨hL, hLH, -⟩ := hM
  cases t <;> simp [Model.θ] <;> linarith

/-- Regime γk < s (q* = γθ/(s+γk)): the payoff comparison of the high type. -/
lemma regB (θH θL γ s k a q : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hk : 0 < k) (hs : 0 < s) (ha : a * (s + γ * k) = γ) (ha0 : 0 < a)
    (h2a : a * (2 * k) ≤ 1) (hr1 : θH * ((1 - γ) * s) < γ * (s + k) * θL)
    (hq0 : 0 ≤ q) (hq : q ≤ a * θH) :
    (1 - γ) * (θH * q - k * q ^ 2) <
      γ * ((θH - θL) * (a * θL)) + (1 - γ) * (θH * (a * θL) - k * (a * θL) ^ 2) := by
  have hD : 0 < s + γ * k := by positivity
  have hg : 0 < 1 - γ := by linarith
  have hgmono : θH * q - k * q ^ 2 ≤ θH * (a * θH) - k * (a * θH) ^ 2 := by
    have e : θH * (a * θH) - k * (a * θH) ^ 2 - (θH * q - k * q ^ 2)
        = (a * θH - q) * (θH - k * (a * θH + q)) := by ring
    have h1 : 0 ≤ a * θH - q := by linarith
    have h2 : 0 ≤ θH - k * (a * θH + q) := by
      have := mul_le_mul_of_nonneg_left hq hk.le
      have h3 : k * (a * θH) * 2 ≤ θH := by nlinarith
      nlinarith
    nlinarith [mul_nonneg h1 h2]
  have hKD : ((γ + (1 - γ) * a * k) * θL - (1 - γ) * (1 - a * k) * θH) * (s + γ * k) =
      γ * (s + k) * θL - (1 - γ) * s * θH := by
    linear_combination ((1 - γ) * k * θL + (1 - γ) * k * θH) * ha
  have hK : 0 < (γ + (1 - γ) * a * k) * θL - (1 - γ) * (1 - a * k) * θH := by
    have : 0 < ((γ + (1 - γ) * a * k) * θL - (1 - γ) * (1 - a * k) * θH) * (s + γ * k) := by
      rw [hKD]; nlinarith
    exact (pos_iff_pos_of_mul_pos this).2 hD
  have hid : γ * ((θH - θL) * (a * θL)) + (1 - γ) * (θH * (a * θL) - k * (a * θL) ^ 2)
      - (1 - γ) * (θH * (a * θH) - k * (a * θH) ^ 2)
      = a * (θH - θL) * ((γ + (1 - γ) * a * k) * θL - (1 - γ) * (1 - a * k) * θH) := by ring
  have : 0 < a * (θH - θL) * ((γ + (1 - γ) * a * k) * θL - (1 - γ) * (1 - a * k) * θH) := by
    have : 0 < θH - θL := by linarith
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hgmono hg.le]

/-- Regime γk ≥ s (q* = θ/(2k)): the payoff comparison of the high type. -/
lemma regA (θH θL γ k q : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hk : 0 < k) (hr2 : θH * (1 - γ) < (1 + γ) * θL) :
    (1 - γ) * (θH * q - k * q ^ 2) <
      γ * ((θH - θL) * (θL / (2 * k))) + (1 - γ) * (θH * (θL / (2 * k)) - k * (θL / (2 * k)) ^ 2) := by
  have hg : 0 < 1 - γ := by linarith
  have hgv : θH * q - k * q ^ 2 ≤ θH * (θH / (2 * k)) - k * (θH / (2 * k)) ^ 2 := by
    have e : θH * (θH / (2 * k)) - k * (θH / (2 * k)) ^ 2 - (θH * q - k * q ^ 2)
        = k * (q - θH / (2 * k)) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hk.le (sq_nonneg (q - θH / (2 * k)))]
  have hid : γ * ((θH - θL) * (θL / (2 * k))) + (1 - γ) * (θH * (θL / (2 * k)) - k * (θL / (2 * k)) ^ 2)
      - (1 - γ) * (θH * (θH / (2 * k)) - k * (θH / (2 * k)) ^ 2)
      = (θH - θL) * ((1 + γ) * θL - (1 - γ) * θH) / (4 * k) := by
    field_simp; ring
  have : 0 < (θH - θL) * ((1 + γ) * θL - (1 - γ) * θH) / (4 * k) := by
    apply div_pos _ (by positivity)
    apply mul_pos <;> linarith
  nlinarith [mul_le_mul_of_nonneg_left hgv hg.le]

theorem high_mimics_low (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < min M.LambdaH1 M.LambdaH2) :
    ¬ ∃ (req : BType → ℝ) (bel : ℝ → BType), M.OSepEq req bel := by
  rintro ⟨req, bel, heq⟩
  have hqL := CustomerVoice.ONoOther.low_request_first_best M hM hr req bel heq
  obtain ⟨hnn, hne, hbel, hopt⟩ := heq
  have hM' := hM
  obtain ⟨hL, hLH, hα0, hα1, hγ0, hγ1, hk, hs⟩ := hM'
  have hD : 0 < M.s + M.γ * M.k := by positivity
  have hg : 0 < 1 - M.γ := by linarith
  rw [lt_min_iff] at hr
  obtain ⟨hr1, hr2⟩ := hr
  unfold Model.LambdaH1 at hr1
  unfold Model.LambdaH2 at hr2
  rw [div_lt_div_iff₀ hL (by positivity)] at hr1 hr2
  obtain ⟨a, ha_def⟩ : ∃ a, a = M.γ / (M.s + M.γ * M.k) := ⟨_, rfl⟩
  have ha : a * (M.s + M.γ * M.k) = M.γ := by rw [ha_def]; exact div_mul_cancel₀ _ hD.ne'
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have hcL : M.γ * M.θL / (M.s + M.γ * M.k) = a * M.θL := by rw [ha_def]; ring
  have hcH : M.γ * M.θH / (M.s + M.γ * M.k) = a * M.θH := by rw [ha_def]; ring
  have hqs_eq : M.qStar M.θL = min (a * M.θL) (M.θL / (2 * M.k)) := by
    rw [Model.qStar, hcL]
  obtain ⟨qs, hqs_def⟩ : ∃ x, x = M.qStar M.θL := ⟨_, rfl⟩
  rw [← hqs_def] at hqL hqs_eq
  have hqs_pos : 0 < qs := by rw [hqs_eq]; exact lt_min (by positivity) (by positivity)
  have hqs_le : qs ≤ a * M.θL := by rw [hqs_eq]; exact min_le_left _ _
  have hqs_le2 : qs ≤ M.θL / (2 * M.k) := by rw [hqs_eq]; exact min_le_right _ _
  have hqs_le2' : 2 * M.k * qs ≤ M.θL := by
    rw [le_div_iff₀ (by positivity)] at hqs_le2; linarith
  have hgqs : 0 < M.θH * qs - M.k * qs ^ 2 := by nlinarith
  have hRpos : 0 < M.γ * ((M.θH - M.θL) * qs) + (1 - M.γ) * (M.θH * qs - M.k * qs ^ 2) := by
    have : 0 < (M.θH - M.θL) * qs := mul_pos (by linarith) hqs_pos
    positivity
  have hdev : M.γ * ((M.θH - M.θL) * qs) + (1 - M.γ) * (M.θH * qs - M.k * qs ^ 2)
      ≤ M.pay bel .H (req .L) := by
    rw [hqL]
    have hb : bel qs = .L := by rw [← hqL]; exact hbel .L
    have hacc : M.accepts (M.θ (bel qs)) qs := by
      rw [hb]; apply accepts_of_le M hM hqs_pos.le
      rw [θL_eq, hcL]; exact hqs_le
    simp only [Model.pay]
    rw [if_pos hacc, hb]
    simp only [Model.mu, θH_eq, θL_eq]
    have m1 : M.θH * qs - M.θL * qs ≤ max (M.θH * qs - M.θL * qs) 0 := le_max_left _ _
    have m2 : M.θH * qs - M.k * qs ^ 2 ≤ max (M.θH * qs - M.k * qs ^ 2) 0 := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_left m1 hγ0.le, mul_le_mul_of_nonneg_left m2 hg.le]
  have hopt' := hopt .H (req .L) (hnn .L)
  have heqp : M.pay bel .H (req .H) <
      M.γ * ((M.θH - M.θL) * qs) + (1 - M.γ) * (M.θH * qs - M.k * qs ^ 2) := by
    have hqH0 : 0 ≤ req .H := hnn .H
    have hb : bel (req .H) = .H := hbel .H
    simp only [Model.pay]
    split_ifs with hacc
    · rw [hb, θH_eq] at hacc
      rw [hb]
      have hqHle : req .H ≤ a * M.θH := by
        have := accepts_le M hM (by linarith) hqH0 hacc
        rwa [hcH] at this
      simp only [Model.mu, θH_eq, sub_self, max_self, mul_zero, zero_add]
      suffices hs' : (1 - M.γ) * (M.θH * req .H - M.k * req .H ^ 2) <
          M.γ * ((M.θH - M.θL) * qs) + (1 - M.γ) * (M.θH * qs - M.k * qs ^ 2) by
        rcases le_total (M.θH * req .H - M.k * req .H ^ 2) 0 with h0 | h0
        · rw [max_eq_right h0]; linarith
        · rw [max_eq_left h0]; exact hs'
      rcases le_total (a * M.θL) (M.θL / (2 * M.k)) with hc | hc
      · have hqsc : qs = a * M.θL := by rw [hqs_eq]; exact min_eq_left hc
        have h2a : a * (2 * M.k) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hc
          nlinarith
        rw [hqsc]
        exact regB M.θH M.θL M.γ M.s M.k a (req .H) hL hLH hγ0 hγ1 hk hs ha ha0 h2a hr1 hqH0 hqHle
      · have hqsc : qs = M.θL / (2 * M.k) := by rw [hqs_eq]; exact min_eq_right hc
        rw [hqsc]
        exact regA M.θH M.θL M.γ M.k (req .H) hL hLH hγ0 hγ1 hk hr2
    · exact hRpos
  linarith

end CustomerVoice.ONoOther.HMLProof

open CustomerVoice.ONoOther in
theorem solution (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < min M.LambdaH1 M.LambdaH2) :
    ¬ ∃ (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType), M.OSepEq req bel :=
  CustomerVoice.ONoOther.HMLProof.high_mimics_low M hM hr

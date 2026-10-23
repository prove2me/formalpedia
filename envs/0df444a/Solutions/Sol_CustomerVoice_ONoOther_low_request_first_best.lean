-- Prove2me | solution 1 for CustomerVoice.ONoOther.low_request_first_best
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:38:20.695141+00:00
-- url     : https://prove2.me/submissions/3676b7c3-4dee-455f-bc29-08837aa88650

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting

namespace CustomerVoice.ONoOther.LRFBProof
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

theorem low_request_first_best (M : Model) (hM : M.Standing)
    (req : BType → ℝ) (bel : ℝ → BType) (heq : M.OSepEq req bel) :
    req .L = M.qStar M.θL := by
  obtain ⟨hnn, hne, hbel, hopt⟩ := heq
  have hM' := hM
  obtain ⟨hL, hLH, hα0, hα1, hγ0, hγ1, hk, hs⟩ := hM'
  have hD : 0 < M.s + M.γ * M.k := by positivity
  set cL := M.γ * M.θL / (M.s + M.γ * M.k) with hcL_def
  set qs := M.qStar M.θL with hqs_def
  have hqs_eq : qs = min cL (M.θL / (2 * M.k)) := rfl
  have hcL : 0 < cL := by positivity
  have hqs_pos : 0 < qs := by rw [hqs_eq]; exact lt_min hcL (by positivity)
  have hqs_le : qs ≤ cL := by rw [hqs_eq]; exact min_le_left _ _
  have hqs_le2 : qs ≤ M.θL / (2 * M.k) := by rw [hqs_eq]; exact min_le_right _ _
  have hqs_le2' : 2 * M.k * qs ≤ M.θL := by
    rw [le_div_iff₀ (by positivity)] at hqs_le2; linarith
  have hfqs : 0 < M.θL * qs - M.k * qs ^ 2 := by nlinarith
  -- payoff of the low type at qs
  have hpay_qs : M.pay bel .L qs = (1 - M.γ) * (M.θL * qs - M.k * qs ^ 2) := by
    obtain ⟨hb1, hb2⟩ := theta_bounds M hM (bel qs)
    have hacc : M.accepts (M.θ (bel qs)) qs := by
      apply accepts_of_le M hM hqs_pos.le
      refine le_trans hqs_le ?_
      rw [hcL_def]
      gcongr
    simp only [Model.pay, if_pos hacc, Model.mu]
    have h1 : max (M.θ BType.L * qs - M.θ (bel qs) * qs) 0 = 0 := by
      apply max_eq_right
      rw [θL_eq]
      nlinarith [mul_le_mul_of_nonneg_right hb1 hqs_pos.le]
    have h2 : max (M.θ BType.L * qs - M.k * qs ^ 2) 0 = M.θL * qs - M.k * qs ^ 2 := by
      rw [θL_eq]; exact max_eq_left hfqs.le
    rw [h1, h2]; ring
  by_contra hne'
  have hle := hopt .L qs hqs_pos.le
  rw [hpay_qs] at hle
  set qL := req .L with hqL_def
  have hqL0 : 0 ≤ qL := hnn .L
  have hbelL : bel qL = .L := hbel .L
  have hlt : M.pay bel .L qL < (1 - M.γ) * (M.θL * qs - M.k * qs ^ 2) := by
    simp only [Model.pay]
    split_ifs with hacc
    · rw [hbelL, θL_eq] at hacc
      rw [hbelL]
      have hqLle : qL ≤ cL := accepts_le M hM hL.le hqL0 hacc
      have hf : M.θL * qL - M.k * qL ^ 2 < M.θL * qs - M.k * qs ^ 2 := by
        rcases le_total cL (M.θL / (2 * M.k)) with hc | hc
        · have hqsc : qs = cL := by rw [hqs_eq]; exact min_eq_left hc
          have hlt : qL < qs := lt_of_le_of_ne (hqsc ▸ hqLle) hne'
          nlinarith [mul_pos (sub_pos.mpr hlt) hk]
        · have hqsc : qs = M.θL / (2 * M.k) := by rw [hqs_eq]; exact min_eq_right hc
          have h2 : 2 * M.k * qs = M.θL := by rw [hqsc]; field_simp
          have hsq : 0 < (qL - qs) ^ 2 := by
            have : qL - qs ≠ 0 := sub_ne_zero.mpr hne'
            positivity
          nlinarith [mul_pos hk hsq]
      simp only [Model.mu, θL_eq, sub_self, max_self]
      rw [mul_zero, zero_add]
      have : max (M.θL * qL - M.k * qL ^ 2) 0 < M.θL * qs - M.k * qs ^ 2 := max_lt hf hfqs
      have hg : 0 < 1 - M.γ := by linarith
      nlinarith
    · have hg : 0 < 1 - M.γ := by linarith
      positivity
  linarith

end CustomerVoice.ONoOther.LRFBProof

open CustomerVoice.ONoOther in
theorem solution (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < min M.LambdaH1 M.LambdaH2)
    (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType) (heq : M.OSepEq req bel) :
    req .L = M.qStar M.θL :=
  CustomerVoice.ONoOther.LRFBProof.low_request_first_best M hM req bel heq

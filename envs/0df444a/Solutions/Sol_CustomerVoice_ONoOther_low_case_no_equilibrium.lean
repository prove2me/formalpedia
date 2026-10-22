-- Prove2me | solution 1 for CustomerVoice.ONoOther.low_case_no_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:45:25.900667+00:00
-- url     : https://prove2.me/submissions/518b729c-57ac-4cd3-82fb-6900c20c64f3

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting
set_option autoImplicit false
open CustomerVoice.ONoOther
open CustomerVoice.ALearn (BType)

open Classical in
lemma cv_pay (M : Model) (bel : ℝ → BType) (t : BType) (q : ℝ) :
    M.pay bel t q = if M.accepts (M.θ (bel q)) q then M.mu q (M.θ t) (M.θ (bel q)) else 0 := rfl

lemma cv_theta_ge (M : Model) (hM : M.Standing) (b : BType) : M.θL ≤ M.θ b := by
  obtain ⟨hθL, hθ, _⟩ := hM
  cases b
  · show M.θL ≤ M.θH; linarith
  · exact le_refl _

lemma cv_L1 (M : Model) (hM : M.Standing) (req : BType → ℝ) (bel : ℝ → BType)
    (heq : M.OSepEq req bel) (t : BType) : req t ≤ M.γ * M.θ t / (M.s + M.γ * M.k) := by
  have hM' := hM
  obtain ⟨hθL, hθ, hα0, hα1, hγ0, hγ1, hk, hs⟩ := hM
  obtain ⟨hnn, hne, hbel, hbr⟩ := heq
  have hθt := cv_theta_ge M hM' t
  have hden : 0 < M.s + M.γ * M.k := by positivity
  by_contra hcon
  push_neg at hcon
  have hb : bel (req t) = t := hbel t
  have hqpos : 0 < req t :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg hγ0.le (by linarith)) hden.le) hcon
  have hmul : M.γ * M.θ t < (M.s + M.γ * M.k) * req t := by
    rw [div_lt_iff₀ hden] at hcon; linarith
  have hpay0 : M.pay bel t (req t) = 0 := by
    rw [cv_pay, if_neg]
    unfold Model.accepts
    rw [hb]
    push_neg
    nlinarith
  have hq'pos : 0 < min (M.γ * M.θL / (M.s + M.γ * M.k)) (M.θ t / (2 * M.k)) :=
    lt_min (by positivity) (div_pos (by linarith) (by positivity))
  set q' := min (M.γ * M.θL / (M.s + M.γ * M.k)) (M.θ t / (2 * M.k)) with hq'
  have hq'1 : q' ≤ M.γ * M.θL / (M.s + M.γ * M.k) := min_le_left _ _
  have hq'2 : q' ≤ M.θ t / (2 * M.k) := min_le_right _ _
  have hq'3 : (M.s + M.γ * M.k) * q' ≤ M.γ * M.θL := by
    rw [le_div_iff₀ hden] at hq'1; linarith
  have hq'4 : 2 * M.k * q' ≤ M.θ t := by
    rw [le_div_iff₀ (by positivity)] at hq'2; linarith
  have hdev := hbr t q' hq'pos.le
  rw [hpay0, cv_pay] at hdev
  have hacc : M.accepts (M.θ (bel q')) q' := by
    unfold Model.accepts
    have h4 := cv_theta_ge M hM' (bel q')
    have h5 : (M.s + M.γ * M.k) * q' ≤ M.γ * M.θ (bel q') := by
      nlinarith [mul_le_mul_of_nonneg_left h4 hγ0.le]
    have h6 : M.γ * (M.θ (bel q') * q' - M.k * q' ^ 2) - M.s * q' ^ 2
        = q' * (M.γ * M.θ (bel q') - (M.s + M.γ * M.k) * q') := by ring
    rw [h6]
    exact mul_nonneg hq'pos.le (sub_nonneg.mpr h5)
  rw [if_pos hacc] at hdev
  unfold Model.mu at hdev
  have h1 : 0 ≤ M.γ * max (M.θ t * q' - M.θ (bel q') * q') 0 := mul_nonneg hγ0.le (le_max_right _ _)
  have h2 : 0 < (1 - M.γ) * max (M.θ t * q' - M.k * q' ^ 2) 0 := by
    apply mul_pos (by linarith)
    apply lt_of_lt_of_le _ (le_max_left _ _)
    nlinarith
  linarith

theorem solution (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < M.LambdaL) :
    ¬ ∃ (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType), M.OSepEq req bel := by
  rintro ⟨req, bel, heq⟩
  have hM' := hM
  obtain ⟨hθL, hθ, hα0, hα1, hγ0, hγ1, hk, hs⟩ := hM
  have heq' := heq
  obtain ⟨hnn, hne, hbel, hbr⟩ := heq
  have hden : 0 < M.s + M.γ * M.k := by positivity
  have hgk : 0 < M.γ * M.k := mul_pos hγ0 hk
  -- γ k < s
  have h1 : 1 < M.θH / M.θL := by rw [lt_div_iff₀ hθL]; linarith
  have h2 : 1 < M.s / (M.γ * M.k) := by
    have := hr; unfold Model.LambdaL at this; linarith
  have h3 : M.γ * M.k < M.s := by rwa [one_lt_div hgk] at h2
  have hr' : M.θH * (M.γ * M.k) < M.s * M.θL := by
    have := hr; unfold Model.LambdaL at this
    rw [div_lt_div_iff₀ hθL hgk] at this; linarith
  set qH := req .H with hqH
  set qL := req .L with hqL
  have hqH0 : 0 ≤ qH := hnn .H
  have hqL0 : 0 ≤ qL := hnn .L
  have hH1 : qH ≤ M.γ * M.θH / (M.s + M.γ * M.k) := cv_L1 M hM' req bel heq' .H
  have hL1 : qL ≤ M.γ * M.θL / (M.s + M.γ * M.k) := cv_L1 M hM' req bel heq' .L
  have hH2 : (M.s + M.γ * M.k) * qH ≤ M.γ * M.θH := by
    rw [le_div_iff₀ hden] at hH1; linarith
  have hL2 : (M.s + M.γ * M.k) * qL ≤ M.γ * M.θL := by
    rw [le_div_iff₀ hden] at hL1; linarith
  -- acceptance of the equilibrium requests
  have accH : M.accepts M.θH qH := by
    unfold Model.accepts
    have : M.γ * (M.θH * qH - M.k * qH ^ 2) - M.s * qH ^ 2
        = qH * (M.γ * M.θH - (M.s + M.γ * M.k) * qH) := by ring
    rw [this]; exact mul_nonneg hqH0 (by linarith)
  have accL : M.accepts M.θL qL := by
    unfold Model.accepts
    have : M.γ * (M.θL * qL - M.k * qL ^ 2) - M.s * qL ^ 2
        = qL * (M.γ * M.θL - (M.s + M.γ * M.k) * qL) := by ring
    rw [this]; exact mul_nonneg hqL0 (by linarith)
  have hθH : M.θ .H = M.θH := rfl
  have hθL' : M.θ .L = M.θL := rfl
  have hH3 : 2 * M.k * qH ≤ M.θH := by nlinarith
  have hL3 : 2 * M.k * qL ≤ M.θL := by nlinarith
  have key : ∀ t' t : BType, M.pay bel t (req t') = M.mu (req t') (M.θ t) (M.θ t') := by
    intro t' t
    have hacc : M.accepts (M.θ t') (req t') := by
      unfold Model.accepts
      have h1 := cv_L1 M hM' req bel heq' t'
      have hθt : 0 < M.θ t' := by
        have := cv_theta_ge M hM' t'; linarith
      have h2 : (M.s + M.γ * M.k) * req t' ≤ M.γ * M.θ t' := by
        rw [le_div_iff₀ hden] at h1; linarith
      have h6 : M.γ * (M.θ t' * req t' - M.k * req t' ^ 2) - M.s * req t' ^ 2
          = req t' * (M.γ * M.θ t' - (M.s + M.γ * M.k) * req t') := by ring
      rw [h6]; exact mul_nonneg (hnn t') (by linarith)
    rw [cv_pay, hbel t', if_pos hacc]
  have dHL := hbr .H qL hqL0
  have dLH := hbr .L qH hqH0
  rw [hqL, key .L .H, key .H .H] at dHL
  rw [hqH, key .H .L, key .L .L] at dLH
  rw [← hqL, ← hqH] at dHL dLH
  unfold Model.mu at dHL dLH
  rw [hθH, hθL'] at dHL dLH
  have mH : max (M.θH * qH - M.k * qH ^ 2) 0 = M.θH * qH - M.k * qH ^ 2 := by
    apply max_eq_left
    have : M.θH * qH - M.k * qH ^ 2 = qH * (M.θH - M.k * qH) := by ring
    rw [this]; exact mul_nonneg hqH0 (by nlinarith)
  have mL : max (M.θL * qL - M.k * qL ^ 2) 0 = M.θL * qL - M.k * qL ^ 2 := by
    apply max_eq_left
    have : M.θL * qL - M.k * qL ^ 2 = qL * (M.θL - M.k * qL) := by ring
    rw [this]; exact mul_nonneg hqL0 (by nlinarith)
  rw [sub_self, max_self, mH] at dHL
  rw [sub_self, max_self, mL] at dLH
  have lb1 : M.θH * qL - M.k * qL ^ 2 ≤ max (M.θH * qL - M.k * qL ^ 2) 0 := le_max_left _ _
  have lb2 : (M.θH - M.θL) * qL ≤ max (M.θH * qL - M.θL * qL) 0 := by
    have := le_max_left (M.θH * qL - M.θL * qL) 0; linarith
  have lb3 : M.θL * qH - M.k * qH ^ 2 ≤ max (M.θL * qH - M.k * qH ^ 2) 0 := le_max_left _ _
  have lb4 : 0 ≤ max (M.θL * qH - M.θH * qH) 0 := le_max_right _ _
  have h1γ : 0 < 1 - M.γ := by linarith
  have g1 : M.θL * qH - M.k * qH ^ 2 ≤ M.θL * qL - M.k * qL ^ 2 := by
    have : (1 - M.γ) * (M.θL * qH - M.k * qH ^ 2) ≤ (1 - M.γ) * (M.θL * qL - M.k * qL ^ 2) := by
      linarith [mul_nonneg hγ0.le lb4, mul_le_mul_of_nonneg_left lb3 h1γ.le]
    exact le_of_mul_le_mul_left this h1γ
  have hΔ : 0 < M.θH - M.θL := by linarith
  have g2 : M.θL ≤ M.k * (qH + qL) := by
    have hqlt : qL ≤ (1 - M.γ) * qH := by
      have : (M.θH - M.θL) * qL ≤ (M.θH - M.θL) * ((1 - M.γ) * qH) := by
        linarith [mul_le_mul_of_nonneg_left lb1 h1γ.le, mul_le_mul_of_nonneg_left lb2 hγ0.le,
          mul_le_mul_of_nonneg_left g1 h1γ.le]
      exact le_of_mul_le_mul_left this hΔ
    have hle : qL ≤ qH := by linarith [mul_nonneg hγ0.le hqH0]
    have hlt : qL < qH := lt_of_le_of_ne hle (fun h => hne (h.symm))
    have : (qH - qL) * M.θL ≤ (qH - qL) * (M.k * (qH + qL)) := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  have hsum : (M.s + M.γ * M.k) * (qH + qL) ≤ M.γ * (M.θH + M.θL) := by linarith
  linarith [mul_le_mul_of_nonneg_left g2 hden.le, mul_le_mul_of_nonneg_left hsum hk.le]

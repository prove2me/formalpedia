-- Prove2me | solution 1 for CustomerVoice.ONoOther.equilibrium_requests_accepted
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:44:46.537405+00:00
-- url     : https://prove2.me/submissions/fc5c5e3d-bc6f-491e-bec7-d93438273285

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
    (hr : M.θH / M.θL < M.LambdaL)
    (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType) (heq : M.OSepEq req bel) :
    req .H ≤ M.γ * M.θH / (M.s + M.γ * M.k) ∧
      req .L ≤ M.γ * M.θL / (M.s + M.γ * M.k) :=
  ⟨cv_L1 M hM req bel heq .H, cv_L1 M hM req bel heq .L⟩

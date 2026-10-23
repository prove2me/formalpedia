-- Prove2me | solution 1 for CustomerVoice.OLearn.ic_necessary
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:36:31.134678+00:00
-- url     : https://prove2.me/submissions/b14b218e-0410-449c-9474-a7e879113eb6

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

open CustomerVoice.OLearn in
theorem solution (M : Model) (hM : M.Standing) :
    ∀ bel : ℝ → CustomerVoice.ALearn.BType, M.OSepEq M.qO bel → M.ICH' ∧ M.ICL' := by
  obtain ⟨hL, hLH, -, -, hg0, hg1, hk, hs⟩ := hM
  have hacc : ∀ t : CustomerVoice.ALearn.BType, M.accepts (M.θ t) (M.qO t) := by
    intro t
    have hθ : 0 < M.θ t := by cases t <;> simp [Model.θ] <;> linarith
    have hD : 0 < M.s + M.γ * M.k := by positivity
    have h0 : 0 ≤ M.qO t := by
      unfold Model.qO Model.qStar; apply le_min <;> positivity
    have h1 : M.qO t ≤ M.γ * M.θ t / (M.s + M.γ * M.k) := by
      unfold Model.qO Model.qStar; exact min_le_left _ _
    rw [le_div_iff₀ hD] at h1
    unfold Model.accepts
    have : M.γ * (M.θ t * M.qO t - M.k * M.qO t ^ 2) - M.s * M.qO t ^ 2
        = M.qO t * (M.γ * M.θ t - M.qO t * (M.s + M.γ * M.k)) := by ring
    rw [this]; exact mul_nonneg h0 (by linarith)
  rintro bel ⟨hnn, -, hbel, hIC⟩
  have hpay : ∀ t u : CustomerVoice.ALearn.BType,
      M.pay bel t (M.qO u) = M.mu (M.qO u) (M.θ t) (M.θ u) := by
    intro t u
    unfold Model.pay
    split_ifs with h
    · rw [hbel u]
    · exact absurd (by rw [hbel u]; exact hacc u) h
  have hH := hIC .H (M.qO .L) (hnn .L)
  have hLL := hIC .L (M.qO .H) (hnn .H)
  rw [hpay, hpay] at hH hLL
  exact ⟨hH, hLL⟩

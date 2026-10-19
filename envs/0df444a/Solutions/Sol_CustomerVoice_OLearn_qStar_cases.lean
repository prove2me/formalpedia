-- Prove2me | solution 1 for CustomerVoice.OLearn.qStar_cases
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:18:21.409466+00:00
-- url     : https://prove2.me/submissions/22dc14cf-2506-49d0-b6b5-81afb0d41506

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting
open CustomerVoice.OLearn

theorem solution(M : Model) (hM : M.Standing) (t : CustomerVoice.ALearn.BType) :
    (M.γ ≤ M.s / M.k → M.qStar (M.θ t) = M.γ * M.θ t / (M.s + M.γ * M.k)) ∧
    (M.s / M.k ≤ M.γ → M.qStar (M.θ t) = M.θ t / (2 * M.k)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hM
  have hθ : 0 < M.θ t := by
    cases t <;> simp only [Model.θ] <;> linarith
  have hd : 0 < M.s + M.γ * M.k := by nlinarith [mul_pos h5 h7]
  have h2k : 0 < 2 * M.k := by linarith
  unfold Model.qStar
  constructor
  · intro h
    rw [le_div_iff₀ h7] at h
    apply min_eq_left
    rw [div_le_div_iff₀ hd h2k]
    nlinarith [mul_le_mul_of_nonneg_left h hθ.le]
  · intro h
    rw [div_le_iff₀ h7] at h
    apply min_eq_right
    rw [div_le_div_iff₀ h2k hd]
    nlinarith [mul_le_mul_of_nonneg_left h hθ.le]

-- Prove2me | solution 1 for CustomerVoice.Thresholds.Delta_gt_Lambda_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:25:31.786832+00:00
-- url     : https://prove2.me/submissions/85256043-d23c-4de8-8682-306ae7483752

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting
set_option autoImplicit false

open CustomerVoice.Thresholds

theorem solution (M : Model) (hM : M.Standing) :
    M.Delta > M.Lambda ↔ M.DeltaL > min M.LambdaH1 M.LambdaH2 := by
  obtain ⟨-, -, -, -, hg0, hg1, hk, hs⟩ := hM
  have hg1' : 0 < 1 - M.γ := by linarith
  have hD : 0 < 2 * M.s + M.γ * M.k := by positivity
  have h1 : M.DeltaH < M.LambdaH1 := by
    unfold Model.DeltaH Model.LambdaH1
    rw [div_lt_div_iff₀ (mul_pos hg1' hD) (mul_pos hg1' hs)]
    have key : 0 < M.γ * (1 - M.γ) * (M.k * M.s + M.γ * M.k ^ 2) := by positivity
    nlinarith [key]
  have h2 : M.DeltaH < M.LambdaH2 := by
    unfold Model.DeltaH Model.LambdaH2
    rw [div_lt_div_iff₀ (mul_pos hg1' hD) hg1']
    have key : 0 < (1 - M.γ) * (2 * M.s) := by positivity
    nlinarith [key]
  have h3 : M.LambdaL < M.DeltaL := by
    unfold Model.LambdaL Model.DeltaL
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith [mul_pos hg0 hk]
  have hm : M.DeltaH < min M.LambdaH1 M.LambdaH2 := lt_min h1 h2
  have gen : ∀ a b m l : ℝ, a < m → l < b → (max m l < max a b ↔ b > m) := by
    intro a b m l ha hb
    simp only [lt_max_iff, max_lt_iff]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact absurd h (not_lt.mpr ha.le)
      · exact h
    · intro h
      exact Or.inr ⟨h, hb⟩
  unfold Model.Delta Model.Lambda
  exact gen _ _ _ _ hm h3

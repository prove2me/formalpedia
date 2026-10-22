-- Prove2me | solution 1 for CustomerVoice.ONoOther.low_case_gamma
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:21:08.83163+00:00
-- url     : https://prove2.me/submissions/228b3fe1-0697-4945-a353-c48623122acd

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting
set_option autoImplicit false
open CustomerVoice.ONoOther

theorem solution (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < M.LambdaL) :
    M.γ < M.s / M.k ∧
      ∀ t : CustomerVoice.ALearn.BType,
        M.qStar (M.θ t) = M.γ * M.θ t / (M.s + M.γ * M.k) ∧
        M.γ * M.θ t / (M.s + M.γ * M.k) < M.θ t / (2 * M.k) := by
  obtain ⟨hθL, hθ, hα0, hα1, hγ0, hγ1, hk, hs⟩ := hM
  have h1 : 1 < M.θH / M.θL := by rw [lt_div_iff₀ hθL]; linarith
  have h2 : 1 < M.s / (M.γ * M.k) := by
    have := hr; unfold Model.LambdaL at this; linarith
  have hgk : 0 < M.γ * M.k := mul_pos hγ0 hk
  have h3 : M.γ * M.k < M.s := by rwa [one_lt_div hgk] at h2
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hk]; linarith
  · intro t
    have hθt : 0 < M.θ t := by
      cases t
      · show 0 < M.θH; linarith
      · exact hθL
    have hden : 0 < M.s + M.γ * M.k := by linarith
    have hlt : M.γ * M.θ t / (M.s + M.γ * M.k) < M.θ t / (2 * M.k) := by
      rw [div_lt_div_iff₀ hden (by linarith)]
      nlinarith [mul_pos hθt hk, mul_pos hθt hgk, mul_pos (mul_pos hθt hk) (sub_pos.mpr h3)]
    refine ⟨?_, hlt⟩
    unfold Model.qStar
    exact min_eq_left hlt.le

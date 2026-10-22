-- Prove2me | solution 1 for CustomerVoice.OLearn.seller_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:51:38.374997+00:00
-- url     : https://prove2.me/submissions/e52efec2-cbbf-4714-8821-1bc4479eddba

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

set_option autoImplicit false
open CustomerVoice.OLearn

theorem solution (M : Model) (hM : M.Standing) :
    ∀ t : CustomerVoice.ALearn.BType, ∀ q : ℝ, 0 ≤ q →
      (M.accepts (M.θ t) q ↔ q ≤ M.γ * M.θ t / (M.s + M.γ * M.k)) := by
  obtain ⟨h1, h2, h3, h4, hg, hg1, hk, hs⟩ := hM
  intro t q hq
  have ht : 0 < M.θ t := by
    cases t
    · show 0 < M.θH; linarith
    · show 0 < M.θL; linarith
  have hc : 0 < M.s + M.γ * M.k := by positivity
  unfold Model.accepts
  rw [le_div_iff₀ hc]
  constructor
  · intro h
    rcases eq_or_lt_of_le hq with h0 | h0
    · rw [← h0]; have := mul_pos hg ht; linarith
    · by_contra hcon
      push_neg at hcon
      nlinarith [mul_pos h0 (sub_pos.2 hcon)]
  · intro h
    nlinarith [mul_nonneg hq (sub_nonneg.2 h)]

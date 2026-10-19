-- Prove2me | solution 1 for CustomerVoice.OLearn.lambdaH1_le_lambdaH2_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:05:28.729238+00:00
-- url     : https://prove2.me/submissions/7d9c376e-b6c3-4ae1-b602-0bf3f792d055

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting
open CustomerVoice.OLearn

theorem solution(M : Model) (hM : M.Standing) :
    M.LambdaH1 ≤ M.LambdaH2 ↔ M.γ ≤ M.s / M.k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hM
  unfold Model.LambdaH1 Model.LambdaH2
  have hg : 0 < 1 - M.γ := by linarith
  rw [div_le_div_iff₀ (mul_pos hg h8) hg, le_div_iff₀ h7]
  constructor
  · intro h
    nlinarith [mul_pos hg hg]
  · intro h
    nlinarith [mul_le_mul_of_nonneg_left h hg.le]

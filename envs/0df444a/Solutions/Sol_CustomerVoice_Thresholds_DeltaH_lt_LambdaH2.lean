-- Prove2me | solution 1 for CustomerVoice.Thresholds.DeltaH_lt_LambdaH2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:03:56.144525+00:00
-- url     : https://prove2.me/submissions/2bf4a27e-66ac-4e03-812e-264bb3f8cae6

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting
open CustomerVoice.Thresholds

theorem solution(M : Model) (hM : M.Standing) :
    M.DeltaH < M.LambdaH2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hM
  unfold Model.DeltaH Model.LambdaH2
  have hg : 0 < 1 - M.γ := by linarith
  have hd : 0 < 2 * M.s + M.γ * M.k := by nlinarith [mul_pos h5 h7]
  rw [div_lt_div_iff₀ (mul_pos hg hd) hg]
  nlinarith [mul_pos hg h8, mul_pos (mul_pos hg h8) hg]

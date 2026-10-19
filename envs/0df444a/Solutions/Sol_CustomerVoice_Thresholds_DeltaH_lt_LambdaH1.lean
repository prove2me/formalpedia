-- Prove2me | solution 1 for CustomerVoice.Thresholds.DeltaH_lt_LambdaH1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:05:20.744387+00:00
-- url     : https://prove2.me/submissions/5a1b3220-e51d-40d1-952a-eaea8bea2c55

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting
open CustomerVoice.Thresholds

theorem solution(M : Model) (hM : M.Standing) :
    M.DeltaH < M.LambdaH1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hM
  unfold Model.DeltaH Model.LambdaH1
  have hg : 0 < 1 - M.γ := by linarith
  have hd : 0 < 2 * M.s + M.γ * M.k := by nlinarith [mul_pos h5 h7]
  have hsk : 0 < M.s + M.γ * M.k := by nlinarith [mul_pos h5 h7]
  have hpos : 0 < M.γ * (1 - M.γ) * M.k * (M.s + M.γ * M.k) :=
    mul_pos (mul_pos (mul_pos h5 hg) h7) hsk
  rw [div_lt_div_iff₀ (mul_pos hg hd) (mul_pos hg h8)]
  nlinarith [hpos]

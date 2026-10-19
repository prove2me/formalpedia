-- Prove2me | solution 1 for CustomerVoice.Thresholds.DeltaL_gt_LambdaL
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:03:57.766576+00:00
-- url     : https://prove2.me/submissions/88c2b24c-cf44-4fb3-a945-abb279d6dca3

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting
open CustomerVoice.Thresholds

theorem solution(M : Model) (hM : M.Standing) :
    M.DeltaL > M.LambdaL := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hM
  unfold Model.DeltaL Model.LambdaL
  have hgk : 0 < M.γ * M.k := mul_pos h5 h7
  apply div_lt_div_of_pos_right _ hgk
  linarith

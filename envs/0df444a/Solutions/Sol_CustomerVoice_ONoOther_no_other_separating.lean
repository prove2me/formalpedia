-- Prove2me | solution 1 for CustomerVoice.ONoOther.no_other_separating
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:42:40.868283+00:00
-- url     : https://prove2.me/submissions/9da12a3d-1e98-4288-a3e3-00bc4e98d46c

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting
import Theorems.Thm_CustomerVoice_ONoOther_high_mimics_low
import Theorems.Thm_CustomerVoice_ONoOther_low_case_no_equilibrium

open CustomerVoice.ONoOther in
theorem solution (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < M.Lambda) :
    ¬ ∃ (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType), M.OSepEq req bel := by
  unfold Model.Lambda at hr
  rcases lt_max_iff.mp hr with h | h
  · exact CustomerVoice.ONoOther.high_mimics_low M hM h
  · exact CustomerVoice.ONoOther.low_case_no_equilibrium M hM h

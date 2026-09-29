-- Prove2me | solution 2 for Freiman.lowerHistory_source_choices
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:35:12.817396+00:00
-- url     : https://prove2.me/submissions/03322aa7-34a1-4f4a-9e80-df7482f3cbbe

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Theorems.Thm_Freiman_lowerHistory_source_choices_from_tails

open Freiman

-- The unconditional choice law follows from the tails version by supplying the Proved
-- theta-value hypothesis.
theorem solution : LowerHistoryChoiceLaw :=
  lowerHistory_source_choices_from_tails lowerHistory_theta_values

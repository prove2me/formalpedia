-- Prove2me | solution 1 for Freiman.lowerHistory_source_choices
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:50.089922+00:00
-- url     : https://prove2.me/submissions/97fb8afb-e1b0-42f4-9bda-247f39194a5e

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_source_choices_from_tails
import Theorems.Thm_Freiman_lowerHistory_theta_values

open Freiman

theorem solution :
    LowerHistoryChoiceLaw := by
  exact lowerHistory_source_choices_from_tails lowerHistory_theta_values

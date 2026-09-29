-- Prove2me | solution 1 for Freiman.lowerHistory_pull_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:35.104005+00:00
-- url     : https://prove2.me/submissions/2a442cb2-e82a-4bd7-a743-97ef7ee95da4

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_pull_from_mobius
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_inv_value

open Freiman

theorem solution :
    LowerHistoryPullLaw := by
  exact lowerHistory_pull_from_mobius lowerHistory_cf_value lowerHistory_inv_value

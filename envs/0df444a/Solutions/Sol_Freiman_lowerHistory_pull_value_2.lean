-- Prove2me | solution 2 for Freiman.lowerHistory_pull_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:25:47.789788+00:00
-- url     : https://prove2.me/submissions/1f0b95bd-0dc2-47c3-9044-e7c3a2a5a932

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_pull_from_mobius
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_inv_value

open Freiman

theorem solution : LowerHistoryPullLaw := by
  apply lowerHistory_pull_from_mobius
  · intro w z hz
    exact lowerHistory_cf_value w z hz
  · intro z hz
    exact lowerHistory_inv_value z hz

-- Prove2me | solution 2 for Freiman.lowerHistory_goodness_semantics
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:38:01.225762+00:00
-- url     : https://prove2.me/submissions/111b9cce-de2d-48f0-9a53-44f48e2d9ca6

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_goodness_from_endpoints
import Theorems.Thm_Freiman_lowerHistory_endpoint_semantics
import Theorems.Thm_Freiman_lowerHistory_greater_semantics

open Freiman

theorem solution : LowerHistoryGoodnessLaw := by
  have hg : LowerHistoryGreaterLaw := lowerHistory_greater_semantics
  have he : LowerHistoryEndpointLaw := lowerHistory_endpoint_semantics
  exact lowerHistory_goodness_from_endpoints hg he

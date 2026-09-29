-- Prove2me | solution 1 for Freiman.lowerHistory_goodness_from_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:48:47.118316+00:00
-- url     : https://prove2.me/submissions/775f4192-56ae-4d23-8793-b1ea91b12b03

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_goodness_semantics

open Freiman

theorem solution (_hg : LowerHistoryGreaterLaw) (_he : LowerHistoryEndpointLaw) :
    LowerHistoryGoodnessLaw := by
  exact lowerHistory_goodness_semantics

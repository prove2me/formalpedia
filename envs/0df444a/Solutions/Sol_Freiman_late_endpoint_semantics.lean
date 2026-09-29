-- Prove2me | solution 1 for Freiman.late_endpoint_semantics
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:30.887233+00:00
-- url     : https://prove2.me/submissions/6088762b-d1de-4589-b4e8-f84e39c579b3

import Theorems.Thm_Freiman_late_endpoint_from_width_cf
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : lateEndpointLaw := by
  exact late_endpoint_from_width_cf lowerHistory_cf_value lowerHistory_width_threshold

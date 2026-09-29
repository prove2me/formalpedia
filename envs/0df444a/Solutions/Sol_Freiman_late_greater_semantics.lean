-- Prove2me | solution 1 for Freiman.late_greater_semantics
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:45.60186+00:00
-- url     : https://prove2.me/submissions/88a1918f-4114-4fb5-8ade-1ba36c047008

import Theorems.Thm_Freiman_late_greater_from_sign
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : lateGreaterLaw := by
  exact late_greater_from_sign lowerHistory_sign_value

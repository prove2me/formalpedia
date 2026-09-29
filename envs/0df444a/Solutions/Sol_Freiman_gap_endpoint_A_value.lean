-- Prove2me | solution 1 for Freiman.gap_endpoint_A_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:40:53.04467+00:00
-- url     : https://prove2.me/submissions/adb0690f-00f7-422d-86e9-bcbf845a7edb

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_join_centre
import Theorems.Thm_Freiman_gap_eventually_periodic_value
import Theorems.Thm_Freiman_gap_period_S_value
import Theorems.Thm_Freiman_gap_endpoint_A_arithmetic
import Theorems.Thm_Freiman_gap_period_T_value

open Freiman

theorem solution : localValue gapExtremizerA 0 = gapLeft := by
  rw [gapExtremizerA, gap_join_centre]
  unfold gapALeft gapARight
  rw [gap_eventually_periodic_value [3,1,3,1,2,1,1,3,3], gap_eventually_periodic_value [3,1,3,1,3]]
  simpa only [gap_period_S_value, gap_period_T_value] using gap_endpoint_A_arithmetic

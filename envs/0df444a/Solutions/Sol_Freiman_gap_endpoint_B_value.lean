-- Prove2me | solution 1 for Freiman.gap_endpoint_B_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:40:53.167127+00:00
-- url     : https://prove2.me/submissions/61dd1494-fc72-4508-b01c-6e7271ff7d46

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_join_centre
import Theorems.Thm_Freiman_gap_eventually_periodic_value
import Theorems.Thm_Freiman_gap_period_S_value
import Theorems.Thm_Freiman_gap_endpoint_B_arithmetic

open Freiman

theorem solution : localValue gapExtremizerB 0 = cF := by
  rw [gapExtremizerB, gap_join_centre]
  unfold gapBLeft gapBRight
  rw [gap_eventually_periodic_value [3,2,1,1], gap_eventually_periodic_value [4,3,2,2]]
  simpa only [gap_period_S_value] using gap_endpoint_B_arithmetic

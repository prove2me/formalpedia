-- Prove2me | solution 1 for Freiman.gap_period_S_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:40:41.844405+00:00
-- url     : https://prove2.me/submissions/d9a0cfad-11d2-45bc-9975-e34f227ea26d

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_periodic_evaluation
import Theorems.Thm_Freiman_gap_period_S_arithmetic

open Freiman

theorem solution : cfValue (gapEventuallyPeriodic [] [3,1,3,1,2,1]) = gapPeriodSValue := by
  exact gap_periodic_evaluation [3,1,3,1,2,1] (by decide) gapPeriodSValue gap_period_S_arithmetic.1 gap_period_S_arithmetic.2

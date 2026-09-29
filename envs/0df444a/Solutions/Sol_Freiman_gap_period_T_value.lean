-- Prove2me | solution 1 for Freiman.gap_period_T_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:40:41.889385+00:00
-- url     : https://prove2.me/submissions/6ac7cfa6-2a3e-4ca9-a910-2bedc42fa11d

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_periodic_evaluation
import Theorems.Thm_Freiman_gap_period_T_arithmetic

open Freiman

theorem solution : cfValue (gapEventuallyPeriodic [] [4,4,4,3,2,3]) = gapPeriodTValue := by
  exact gap_periodic_evaluation [4,4,4,3,2,3] (by decide) gapPeriodTValue gap_period_T_arithmetic.1 gap_period_T_arithmetic.2

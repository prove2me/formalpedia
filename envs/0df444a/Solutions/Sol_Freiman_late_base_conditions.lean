-- Prove2me | solution 1 for Freiman.late_base_conditions
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:08:02.581286+00:00
-- url     : https://prove2.me/submissions/732098e2-cdd0-4d57-ad7f-a31890a66edf

import Theorems.Thm_Freiman_late_base_from_theta_width
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) : lateHolds lateRootBounds (lateR p) (lateS p) (lateQ p) := by
  exact late_base_from_theta_width lowerHistory_theta_values lowerHistory_width_threshold t p hs hd

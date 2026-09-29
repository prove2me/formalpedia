-- Prove2me | solution 1 for Freiman.late_decisions_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:15.553689+00:00
-- url     : https://prove2.me/submissions/ae8e277c-00ba-4aa0-a673-51cad52b366c

import Theorems.Thm_Freiman_late_decision_other_valid
import Theorems.Thm_Freiman_late_decision_right3_valid
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : ∀ right3 : Bool, lateDecisionValid lateCatalog right3 lateRootBounds (lateRootRectangle right3) (lateTree right3) := by
  intro right3
  cases right3
  · exact late_decision_other_valid
  · exact late_decision_right3_valid

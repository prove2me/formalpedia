-- Prove2me | solution 1 for Freiman.late_catalog_selection
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:31.088407+00:00
-- url     : https://prove2.me/submissions/e3391aaa-9a01-471a-ac94-8d8085525bac

import Theorems.Thm_Freiman_late_decision_sound
import Theorems.Thm_Freiman_late_proof_sound
import Theorems.Thm_Freiman_late_all_witnesses
import Theorems.Thm_Freiman_late_decisions_valid
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : ∀ right3 : Bool, lateDecisionSound lateCatalog right3 lateRootBounds (lateRootRectangle right3) := by
  intro right3
  exact late_decision_sound lateCatalog (late_proof_sound lateCatalog late_all_witnesses) right3 lateRootBounds (lateRootRectangle right3) (lateTree right3) (late_decisions_valid right3)

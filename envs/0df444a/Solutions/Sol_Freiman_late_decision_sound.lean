-- Prove2me | solution 1 for Freiman.late_decision_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:31.579452+00:00
-- url     : https://prove2.me/submissions/5e25e7d9-a666-410b-9b8b-d7a7a45b5a67

import Theorems.Thm_Freiman_late_decision_from_proofs
import Theorems.Thm_Freiman_lowerHistory_complement
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : ∀ (C : LateCatalog), lateProofSound C → ∀ right3 bs R tr, lateDecisionValid C right3 bs R tr → lateDecisionSound C right3 bs R := by
  exact late_decision_from_proofs lowerHistory_complement

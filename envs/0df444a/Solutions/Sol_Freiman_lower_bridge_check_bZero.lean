-- Prove2me | solution 1 for Freiman.lower_bridge_check_bZero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:49:07.775433+00:00
-- url     : https://prove2.me/submissions/bd6b4a1a-9b36-4eb7-9b10-9e95fd8935e3

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Data.List.Basic

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : DecidablePred lowerBridgeChecked := fun r => by
  unfold lowerBridgeChecked
  infer_instance

theorem solution : ∀ r ∈ lowerBridgeRecords .bZero, lowerBridgeChecked r := by
  have checked : List.Forall lowerBridgeChecked (lowerBridgeRecords .bZero) := by
    decide +kernel
  exact List.forall_iff_forall_mem.mp checked

#print axioms solution

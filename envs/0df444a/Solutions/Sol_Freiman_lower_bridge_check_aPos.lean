-- Prove2me | solution 1 for Freiman.lower_bridge_check_aPos
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:51:20.193912+00:00
-- url     : https://prove2.me/submissions/3b372b92-234e-4d5f-aefa-d54d310242e4

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Data.List.Basic

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : DecidablePred lowerBridgeChecked := fun r => by
  unfold lowerBridgeChecked
  infer_instance

theorem solution : ∀ r ∈ lowerBridgeRecords .aPos, lowerBridgeChecked r := by
  have checked : List.Forall lowerBridgeChecked (lowerBridgeRecords .aPos) := by
    decide +kernel
  exact List.forall_iff_forall_mem.mp checked

#print axioms solution

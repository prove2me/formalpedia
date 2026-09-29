-- Prove2me | solution 1 for Freiman.lower_bridge_check_aZero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:50:34.983725+00:00
-- url     : https://prove2.me/submissions/437a4c41-1763-4026-bf66-34b4bc529b35

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Data.List.Basic

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : DecidablePred lowerBridgeChecked := fun r => by
  unfold lowerBridgeChecked
  infer_instance

theorem solution : ∀ r ∈ lowerBridgeRecords .aZero, lowerBridgeChecked r := by
  have checked : List.Forall lowerBridgeChecked (lowerBridgeRecords .aZero) := by
    decide +kernel
  exact List.forall_iff_forall_mem.mp checked

#print axioms solution

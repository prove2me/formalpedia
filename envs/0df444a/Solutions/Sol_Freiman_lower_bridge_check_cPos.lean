-- Prove2me | solution 1 for Freiman.lower_bridge_check_cPos
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:35:51.316051+00:00
-- url     : https://prove2.me/submissions/71fbda34-81b4-4cc6-bd2a-cc3752f75688

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Data.List.Basic

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : DecidablePred lowerBridgeChecked := fun r => by
  unfold lowerBridgeChecked
  infer_instance

theorem solution : ∀ r ∈ lowerBridgeRecords .cPos, lowerBridgeChecked r := by
  have checked : List.Forall lowerBridgeChecked (lowerBridgeRecords .cPos) := by
    decide +kernel
  exact List.forall_iff_forall_mem.mp checked

#print axioms solution

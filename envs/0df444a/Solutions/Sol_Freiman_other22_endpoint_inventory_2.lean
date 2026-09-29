-- Prove2me | solution 2 for Freiman.other22_endpoint_inventory
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T20:17:45.321964+00:00
-- url     : https://prove2.me/submissions/7642f1b7-a6ed-4cd1-b8fe-dbf9bd90e627

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

set_option autoImplicit false

set_option maxHeartbeats 4000000 in
theorem solution  :
    ∀ k : Fin 6, lowerHistoryEndpointComparisons (other22Paths k) =
    lowerHistoryComparisons (other22Context k) (other22Ancestor k) other22ResidualWords (other22AncestorUpper k) false := by
  decide +kernel

-- Prove2me | solution 1 for Freiman.other22_endpoint_inventory
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T12:22:42.556568+00:00
-- url     : https://prove2.me/submissions/ab556d48-0263-470d-85ea-865ffc58818f

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution :
    ∀ k : Fin 6, lowerHistoryEndpointComparisons (other22Paths k) =
      lowerHistoryComparisons (other22Context k) (other22Ancestor k)
        other22ResidualWords (other22AncestorUpper k) false := by
  intro k
  revert k
  decide +kernel

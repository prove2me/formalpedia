-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_endpoint_order_mixed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:39:20.240801+00:00
-- url     : https://prove2.me/submissions/4a95fb44-ee63-4075-a231-5425977aefe0

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order

open Freiman

theorem solution (p : LowerPair) (_hp : p.1.length % 2 ≠ p.2.length % 2) :
    lowerEndpoint p false ≤ lowerEndpoint p true := by
  exact lowerEarlyTerminal_endpoint_order p

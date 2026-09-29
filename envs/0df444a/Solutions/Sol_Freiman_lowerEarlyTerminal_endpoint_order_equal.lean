-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_endpoint_order_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:38:51.500627+00:00
-- url     : https://prove2.me/submissions/e7ab6057-c7d0-40aa-ba2b-c97fcc175e02

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order

open Freiman

theorem solution (p : LowerPair) (_hp : p.1.length % 2 = p.2.length % 2) :
    lowerEndpoint p false ≤ lowerEndpoint p true := by
  exact lowerEarlyTerminal_endpoint_order p

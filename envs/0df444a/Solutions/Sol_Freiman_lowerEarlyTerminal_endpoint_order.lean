-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_endpoint_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:06.594974+00:00
-- url     : https://prove2.me/submissions/afd889ae-a66a-40af-af69-1e1e16b081f8

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order_equal
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order_mixed

open Freiman

theorem solution (p : LowerPair) : lowerEndpoint p false ≤ lowerEndpoint p true := by
  by_cases h : p.1.length % 2 = p.2.length % 2
  · exact lowerEarlyTerminal_endpoint_order_equal p h
  · exact lowerEarlyTerminal_endpoint_order_mixed p h

-- Prove2me | solution 2 for Freiman.lowerEarlyTerminal_endpoint_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:05:15.595042+00:00
-- url     : https://prove2.me/submissions/54eb5699-2273-469e-b295-81061f1b6d87

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order_equal
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order_mixed

open Freiman

theorem solution (p : LowerPair) : lowerEndpoint p false ≤ lowerEndpoint p true := by
  by_cases hp : p.1.length % 2 = p.2.length % 2
  · exact lowerEarlyTerminal_endpoint_order_equal p hp
  · exact lowerEarlyTerminal_endpoint_order_mixed p hp

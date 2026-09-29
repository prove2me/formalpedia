-- Prove2me | solution 2 for Freiman.lowerEarlyTerminal_endpoint_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:06:45.609229+00:00
-- url     : https://prove2.me/submissions/ad7c0c6c-a405-4e99-87ec-3669dc608ce9

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_equal
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_mixed

open Freiman

theorem solution : LowerEarlyTerminalEndpointLaw := by
  intro base C hc hf w upper
  by_cases he : lowerHistoryWordParity C w false = lowerHistoryWordParity C w true
  · exact lowerEarlyTerminal_endpoint_equal base C hc hf w upper he
  · exact lowerEarlyTerminal_endpoint_mixed base C hc hf w upper he

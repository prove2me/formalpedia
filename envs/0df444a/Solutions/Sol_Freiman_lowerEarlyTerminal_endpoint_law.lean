-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_endpoint_law
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:52.872429+00:00
-- url     : https://prove2.me/submissions/7c32e0de-f968-4317-be00-c444c6a31ffb

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_equal
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_mixed

open Freiman

theorem solution : LowerEarlyTerminalEndpointLaw := by
  intro base C hc hf w upper
  by_cases he : lowerHistoryWordParity C w false = lowerHistoryWordParity C w true
  · exact lowerEarlyTerminal_endpoint_equal base C hc hf w upper he
  · exact lowerEarlyTerminal_endpoint_mixed base C hc hf w upper he

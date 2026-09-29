-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_early3_finite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:37.892926+00:00
-- url     : https://prove2.me/submissions/8ea1a364-5212-4154-bb21-e37adfb4ab7b

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_early3_goal_ids
import Theorems.Thm_Freiman_lowerEarlyTerminal_early3_pairs
import Theorems.Thm_Freiman_lowerEarlyTerminal_early3_records
import Theorems.Thm_Freiman_lowerEarlyTerminal_early3_coverage

open Freiman

theorem solution : lowerEarlyTerminalFiniteValid lowerEarlyTerminalEarly3 := by
  exact ⟨lowerEarlyTerminal_early3_goal_ids, lowerEarlyTerminal_early3_pairs, lowerEarlyTerminal_early3_records, lowerEarlyTerminal_early3_coverage⟩

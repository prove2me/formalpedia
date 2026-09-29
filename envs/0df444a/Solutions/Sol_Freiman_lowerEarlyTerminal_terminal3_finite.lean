-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal3_finite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:37.845297+00:00
-- url     : https://prove2.me/submissions/ce208d36-45f7-4e2c-ac4a-42861a06a403

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_goal_ids
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_records
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_coverage

open Freiman

theorem solution : lowerEarlyTerminalFiniteValid lowerEarlyTerminalTerminal3 := by
  exact ⟨lowerEarlyTerminal_terminal3_goal_ids, lowerEarlyTerminal_terminal3_pairs, lowerEarlyTerminal_terminal3_records, lowerEarlyTerminal_terminal3_coverage⟩

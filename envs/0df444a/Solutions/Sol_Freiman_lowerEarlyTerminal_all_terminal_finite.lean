-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_all_terminal_finite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:53.985341+00:00
-- url     : https://prove2.me/submissions/e3685951-8486-4609-aa2e-67b553e71443

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_finite
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_finite
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_finite

import Mathlib.Tactic.FinCases

open Freiman

theorem solution (i : Fin 3) : lowerEarlyTerminalFiniteValid (lowerEarlyTerminalTerminalCatalog i) := by
  fin_cases i
  · exact lowerEarlyTerminal_state1_finite
  · exact lowerEarlyTerminal_state2_finite
  · exact lowerEarlyTerminal_terminal3_finite

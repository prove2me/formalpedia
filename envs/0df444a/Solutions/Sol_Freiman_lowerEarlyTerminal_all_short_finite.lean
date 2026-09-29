-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_all_short_finite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:55.606032+00:00
-- url     : https://prove2.me/submissions/8f47b80d-ce93-421b-a444-4a3c2a2d8a4a

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_early3_finite
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_finite
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_finite

import Mathlib.Tactic.FinCases

open Freiman

theorem solution (i : Fin 3) : lowerEarlyTerminalFiniteValid (lowerEarlyTerminalShortCatalog i) := by
  fin_cases i
  · exact lowerEarlyTerminal_early3_finite
  · exact lowerEarlyTerminal_state1_finite
  · exact lowerEarlyTerminal_state2_finite

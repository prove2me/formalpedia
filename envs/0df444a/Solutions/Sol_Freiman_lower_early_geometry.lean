-- Prove2me | solution 1 for Freiman.lower_early_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:34.759627+00:00
-- url     : https://prove2.me/submissions/830ba512-1dec-4102-b6fd-3c2427c5a480

import Theorems.Thm_Freiman_lower_early_first_chain
import Theorems.Thm_Freiman_lower_early_second_chain
import Theorems.Thm_Freiman_lower_terminal_suffix_cases
import Theorems.Thm_Freiman_lower_terminal_state1
import Theorems.Thm_Freiman_lower_terminal_state2
import Theorems.Thm_Freiman_lower_terminal_state3
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) : lowerEarlyGeometry p := by
  by_cases h27 : lowerA p 27
  · exact lower_early_first_chain t p hs hd h27
  · by_cases h34 : lowerA p 34
    · exact lower_early_second_chain t p hs hd h27 h34
    · rcases lower_terminal_suffix_cases t p hs with h1 | h2 | h3
      · exact lower_terminal_state1 t p hs hd h27 h34 h1
      · exact lower_terminal_state2 t p hs hd h27 h34 h2
      · exact lower_terminal_state3 t p hs hd h27 h34 h3

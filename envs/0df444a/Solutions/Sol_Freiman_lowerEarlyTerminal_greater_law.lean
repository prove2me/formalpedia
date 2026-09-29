-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_greater_law
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:07.819325+00:00
-- url     : https://prove2.me/submissions/5a54cafd-4837-47d4-950b-3927ca3860a9

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_greater_weak
import Theorems.Thm_Freiman_lowerEarlyTerminal_greater_strict

open Freiman

theorem solution : LowerEarlyTerminalGreaterLaw := by
  intro base C hc hf x y strict hx hy
  cases strict
  · exact lowerEarlyTerminal_greater_weak base C hc hf x y hx hy
  · exact lowerEarlyTerminal_greater_strict base C hc hf x y hx hy

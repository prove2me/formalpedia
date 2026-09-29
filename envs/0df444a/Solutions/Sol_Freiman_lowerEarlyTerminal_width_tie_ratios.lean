-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_width_tie_ratios
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:21.395681+00:00
-- url     : https://prove2.me/submissions/be01ef65-5f94-44ef-b718-9215d95c1f78

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_coefficients
import Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_ratio_factor
import Theorems.Thm_Freiman_lowerJ_width_formula

open Freiman

theorem solution (u v : List ℕ+) (h : lowerWidth u = lowerWidth v) : lowerRatio u = lowerRatio v ∨
      lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u) := by
  exact lowerEarlyTerminal_width_tie_ratio_factor u v
    (lowerEarlyTerminal_width_tie_coefficients lowerJ_width_formula u v h)

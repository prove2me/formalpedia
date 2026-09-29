-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_tie3_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:21.393236+00:00
-- url     : https://prove2.me/submissions/4866de47-1168-4869-892c-60e85addde85

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_coefficients
import Theorems.Thm_Freiman_lowerJ_width_formula
import Theorems.Thm_Freiman_lowerEarlyTerminal_tie3_structure
import Theorems.Thm_Freiman_lowerEarlyTerminal_opposite_parity_cd

open Freiman

theorem solution (ht : ∀ u v : List ℕ+, lowerWidth u = lowerWidth v →
      lowerRatio u = lowerRatio v ∨ lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u))
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l) : ¬ lowerEarlyTerminalTie3 p l := by
  intro he
  obtain ⟨hu,hv,hpar,hcd⟩ := lowerEarlyTerminal_tie3_structure
    (fun u v h => lowerEarlyTerminal_width_tie_coefficients lowerJ_width_formula u v h)
    ht t p hs hd l hn he
  exact lowerEarlyTerminal_opposite_parity_cd
    (lowerEarlyTerminalForkPair p l true 2).1 (lowerEarlyTerminalForkPair p l true 2).2 hu hv hpar hcd

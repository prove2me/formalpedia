-- Prove2me | solution 1 for Freiman.lower_initial_survivor_target
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:48.325865+00:00
-- url     : https://prove2.me/submissions/87f88fcc-c219-444d-859b-97da7745c4cb

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_survivor_large
import Theorems.Thm_Freiman_lower_bridge_survivor_endpoint

open Freiman

theorem solution (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ)
    (hmarked : (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ p = 0))
    (hsafe : lowerInitialSafeBound t f n k p) (s : LowerPair)
    (hnorm : lowerNormalize s =
      ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [1],
       (lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1])) :
    lowerLocalLower s ([2],[2]) ≤ lowerLocalCoordinate s t := by
  exact Freiman.lower_bridge_survivor_endpoint Freiman.lower_bridge_survivor_large t f n k p hmarked hsafe s hnorm

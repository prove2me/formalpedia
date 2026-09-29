-- Prove2me | solution 2 for Freiman.lower_initial_survivor_target
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:53:59.882803+00:00
-- url     : https://prove2.me/submissions/d3156c8e-18e3-4f6e-801f-4bbecc5d8798

import Definitions.Def_Freiman_lowerBridgeCatalog
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_bridge_survivor_large
import Theorems.Thm_Freiman_lower_bridge_survivor_endpoint

open Freiman

-- `lower_bridge_survivor_endpoint` proves exactly this conclusion, but takes the
-- large-survivor family as an extra hypothesis; `lower_bridge_survivor_large` supplies it.
theorem solution (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ)
    (hmarked : (f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0) ∨ (f = .C ∧ p = 0))
    (hsafe : lowerInitialSafeBound t f n k p) (s : LowerPair)
    (hnorm : lowerNormalize s =
      ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [1],
       (lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1])) :
    lowerLocalLower s ([2],[2]) ≤ lowerLocalCoordinate s t :=
  lower_bridge_survivor_endpoint
    (fun c n k hc => lower_bridge_survivor_large c n k hc)
    t f n k p hmarked hsafe s hnorm

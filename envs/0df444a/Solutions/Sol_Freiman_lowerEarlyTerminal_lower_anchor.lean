-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_lower_anchor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:04.942729+00:00
-- url     : https://prove2.me/submissions/a8ce91cf-0a55-47ff-babd-511cefdbe1e1

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_early_geometry

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) :
    lowerLocalLower p ([3],[2]) ≤
    (if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint p false else -lowerEndpoint p true) := by
  rcases trunk_early_geometry t p hs hd with ⟨plan,hg,_,_,hlast⟩
  simpa only [trunkParentEndpoint,Bool.not_false] using hg.lower ([3],[2]) hlast

-- Prove2me | solution 1 for Freiman.lower_geometry_equal_small_left
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:05.028992+00:00
-- url     : https://prove2.me/submissions/97c8140e-235f-4f29-874d-7a46e3378d85

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_active_geometry
import Theorems.Thm_Freiman_trunk_select_geometry_equal_small_left

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ lowerL p) :
    lowerNumericSuccessor t p := by
  exact trunk_select_geometry_equal_small_left t p hs hb hp97 hlate hc (trunk_active_geometry t p hs hc.1)

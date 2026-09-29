-- Prove2me | solution 1 for Freiman.lower_geometry_mixed_three
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:47.472634+00:00
-- url     : https://prove2.me/submissions/23a07e74-e13b-485a-abf2-e02981a46360

import Theorems.Thm_Freiman_section14_select_three
import Theorems.Thm_Freiman_section14_raw_geometry
import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5 ∧ ¬ lowerL p) : lowerNumericSuccessor t p := by
  exact section14_select_three t p hs hb hp97 hlate hc (section14_raw_geometry t p hs hc.1)

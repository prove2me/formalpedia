-- Prove2me | solution 1 for Freiman.lower_geometry_mixed_long
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:47.387466+00:00
-- url     : https://prove2.me/submissions/29e3640f-d9f5-4e00-837f-cc575146d446

import Theorems.Thm_Freiman_section14_select_long
import Theorems.Thm_Freiman_section14_raw_geometry
import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ ¬ lowerH p 5) : lowerNumericSuccessor t p := by
  exact section14_select_long t p hs hb hp97 hlate hc (section14_raw_geometry t p hs hc.1)

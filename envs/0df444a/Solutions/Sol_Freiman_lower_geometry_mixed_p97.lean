-- Prove2me | solution 1 for Freiman.lower_geometry_mixed_p97
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:47.288657+00:00
-- url     : https://prove2.me/submissions/5f08497e-91a6-4e00-94a6-2f46b2b68f9f

import Theorems.Thm_Freiman_section14_select_p97
import Theorems.Thm_Freiman_section14_raw_geometry
import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5 ∧ lowerL p) : lowerNumericSuccessor t p := by
  exact section14_select_p97 t p hs hb hp97 hlate hc (section14_raw_geometry t p hs hc.1)

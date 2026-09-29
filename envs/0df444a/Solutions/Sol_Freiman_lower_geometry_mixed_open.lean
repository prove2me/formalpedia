-- Prove2me | solution 1 for Freiman.lower_geometry_mixed_open
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:12:09.916918+00:00
-- url     : https://prove2.me/submissions/e07fe925-6360-41ec-864e-3d4f08a2d35b

import Theorems.Thm_Freiman_section14_select_open
import Theorems.Thm_Freiman_section14_raw_geometry
import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ lowerH p 2) : lowerNumericSuccessor t p := by
  exact section14_select_open t p hs hb hp97 hlate hc (section14_raw_geometry t p hs hc.1)

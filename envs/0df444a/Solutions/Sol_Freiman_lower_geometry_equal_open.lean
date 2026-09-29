-- Prove2me | solution 1 for Freiman.lower_geometry_equal_open
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:05.233768+00:00
-- url     : https://prove2.me/submissions/4f7f93d1-7e8f-4526-ba39-45638e61afb3

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_active_geometry
import Theorems.Thm_Freiman_trunk_select_geometry_equal_open

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ lowerA p 3) :
    lowerNumericSuccessor t p := by
  exact trunk_select_geometry_equal_open t p hs hb hp97 hlate hc (trunk_active_geometry t p hs hc.1)

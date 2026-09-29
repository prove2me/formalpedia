-- Prove2me | solution 1 for Freiman.lower_geometry_equal_small_plain_with_run
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:06.961012+00:00
-- url     : https://prove2.me/submissions/f0238ef8-029c-4c32-82d5-d3b451c77c40

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_active_geometry
import Theorems.Thm_Freiman_trunk_select_geometry_equal_small_plain_with_run

open Freiman

theorem solution (hJ : ∀ (t : ℝ) (p : LowerPair), lowerState t p → lowerRunOffered p → lowerRunFamily p)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerL p ∧ (¬ lowerR p ∨ lowerA p 16)) :
    lowerNumericSuccessor t p := by
  exact trunk_select_geometry_equal_small_plain_with_run hJ t p hs hb hp97 hlate hc (trunk_active_geometry t p hs hc.1)

-- Prove2me | solution 1 for Freiman.lower_late_parent_gluing
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:22.640988+00:00
-- url     : https://prove2.me/submissions/44336577-b0e4-4dfb-b729-d3a991d4b01b

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_active_geometry
import Theorems.Thm_Freiman_trunk_select_late_parent_gluing

open Freiman

theorem solution (hroute : ∀ (t : ℝ) (p : LowerPair), lowerState t p → (¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) → lowerLateEntryDomain p → ∃ ls : List LowerLabel, lowerLateRouteValid p ls)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p) :
    lowerNumericSuccessor t p := by
  exact trunk_select_late_parent_gluing hroute t p hs hb hp97 hlate hc (trunk_active_geometry t p hs hc.1)

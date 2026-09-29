-- Prove2me | solution 1 for Freiman.lower_early_parent_gluing
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:07.140405+00:00
-- url     : https://prove2.me/submissions/8fcdee9e-ccb1-4a7a-aa03-bbbdbe992333

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_active_geometry
import Theorems.Thm_Freiman_trunk_select_early_parent_gluing

open Freiman

theorem solution (hchain : ∀ (t : ℝ) (p : LowerPair), lowerState t p → lowerEarlyDomain p → lowerEarlyGeometry p)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerL p ∧ lowerR p ∧ ¬ lowerA p 16) :
    lowerNumericSuccessor t p := by
  exact trunk_select_early_parent_gluing hchain t p hs hb hp97 hlate hc (trunk_active_geometry t p hs hc.1)

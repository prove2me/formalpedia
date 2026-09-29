-- Prove2me | solution 1 for Freiman.lower_late_anchor_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:49.163697+00:00
-- url     : https://prove2.me/submissions/abfc226f-513b-4874-938c-df213faf100e

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_late_geometry
import Theorems.Thm_Freiman_lower_strict_good_implies_good

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) :
    lowerGood (lowerChild p ([2],[2])) ∧ lowerGood (lowerChild p ([2],[1])) := by
  rcases trunk_late_geometry t p hs hd with ⟨plan,hg,ha,hb⟩
  exact ⟨lower_strict_good_implies_good _ (hg.strictGood _ ha),
    lower_strict_good_implies_good _ (hg.strictGood _ hb)⟩

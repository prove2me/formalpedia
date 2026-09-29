-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_anchor_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:50.658698+00:00
-- url     : https://prove2.me/submissions/cddf5ea0-c076-4b70-836a-9e65e9c7354a

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_early_geometry
import Theorems.Thm_Freiman_lower_strict_good_implies_good

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) :
    lowerGood (lowerChild p ([3],[2])) ∧ lowerGood (lowerChild p ([2],[2])) := by
  rcases trunk_early_geometry t p hs hd with ⟨plan,hg,ha,hb,_⟩
  exact ⟨lower_strict_good_implies_good _ (hg.strictGood _ ha),
    lower_strict_good_implies_good _ (hg.strictGood _ hb)⟩

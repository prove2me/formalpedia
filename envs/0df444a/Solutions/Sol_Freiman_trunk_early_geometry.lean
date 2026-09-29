-- Prove2me | solution 1 for Freiman.trunk_early_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:49.123488+00:00
-- url     : https://prove2.me/submissions/b33d903b-eeaa-4b0b-8c2b-468b7214e13b

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_active_geometry
import Theorems.Thm_Freiman_trunk_early_plan

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p) :
    ∃ plan : TrunkPlan, TrunkGeometry p plan ∧ ([3],[2]) ∈ plan.labels ∧ ([2],[2]) ∈ plan.labels ∧ plan.labels.getLast? = some ([3],[2]) := by
  rcases trunk_active_geometry t p hs hd.1 with ⟨k,hfit,_,hgeom⟩
  rcases trunk_early_plan t p hs hd k hfit with ⟨pi,hpi,hcuts,hleft,hright,hlast⟩
  exact ⟨_,hgeom pi hpi hcuts,hleft,hright,hlast⟩

-- Prove2me | solution 1 for Freiman.trunk_late_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:49.211436+00:00
-- url     : https://prove2.me/submissions/b94cf743-f41a-4b45-bf75-4700c9ff4bfb

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_active_geometry
import Theorems.Thm_Freiman_trunk_late_plan

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) :
    ∃ plan : TrunkPlan, TrunkGeometry p plan ∧ ([2],[2]) ∈ plan.labels ∧ ([2],[1]) ∈ plan.labels := by
  rcases trunk_active_geometry t p hs hd.1 with ⟨k,hfit,_,hgeom⟩
  rcases trunk_late_plan t p hs hd k hfit with ⟨pi,hpi,hcuts,hleft,hright⟩
  exact ⟨_,hgeom pi hpi hcuts,hleft,hright⟩

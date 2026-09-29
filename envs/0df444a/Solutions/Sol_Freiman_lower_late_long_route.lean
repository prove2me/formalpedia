-- Prove2me | solution 1 for Freiman.lower_late_long_route
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:08:03.653445+00:00
-- url     : https://prove2.me/submissions/4e9ba7af-c7da-4b0c-9988-d3f4dfb704ef

import Theorems.Thm_Freiman_late_parameter_case
import Theorems.Thm_Freiman_late_catalog_selection
import Theorems.Thm_Freiman_late_base_conditions
import Theorems.Thm_Freiman_late_route_geometry
import Theorems.Thm_Freiman_lower_late_anchor_goodness
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p)
    (hr : (13/17 : ℝ) ≤ lowerRatio (lowerNormalize p).1) : ∃ ls : List LowerLabel, lowerLateRouteValid p ls := by
  obtain ⟨right3,hm,hrect⟩ := late_parameter_case t p hs hd hr
  obtain ⟨i,hi,hcase,hrequired⟩ := late_catalog_selection right3 (lateR p) (lateS p) (lateQ p) hrect (late_base_conditions t p hs hd)
  have hm' : lateMatches p (latePath lateCatalog i).right3 := by
    rw [hcase]
    exact hm
  exact ⟨(latePath lateCatalog i).route,
    late_route_geometry p i hi hm' hrequired (lower_late_anchor_goodness t p hs hd)⟩

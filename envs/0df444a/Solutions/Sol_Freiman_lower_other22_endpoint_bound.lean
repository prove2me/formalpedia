-- Prove2me | solution 1 for Freiman.lower_other22_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:13:23.548174+00:00
-- url     : https://prove2.me/submissions/20720814-006d-41e2-b93c-f38ce44d65f8

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_other22_context_cover
import Theorems.Thm_Freiman_other22_geometry_order

open Freiman

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) :
    lowerOther22EndpointBound Z S := by
  classical
  obtain ⟨k,hc⟩ := other22_context_cover Z B R S h
  have ho := other22_geometry_order Z B R S h k hc
  unfold lowerOther22EndpointBound
  unfold other22AnchorValue at ho
  split_ifs at * <;> exact ho

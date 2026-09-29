-- Prove2me | solution 1 for Freiman.trunk_active_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:49.236096+00:00
-- url     : https://prove2.me/submissions/8e062f35-37d0-4686-a7a6-06b5ce073968

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_parameter_state
import Theorems.Thm_Freiman_trunk_parent_mode
import Theorems.Thm_Freiman_trunk_raw_geometry

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (he : ¬ lowerMixed p) :
    TrunkActiveGeometry p := by
  rcases trunk_parameter_state t p hs he with ⟨k,hfit,hrect⟩
  rcases trunk_parent_mode t p hs k hfit with ⟨par,hpar,hparent⟩
  refine ⟨k,hfit,hrect,?_⟩
  intro pi hpi hcuts
  apply trunk_raw_geometry p k pi par
  refine ⟨hfit,hrect,hpi,hpar,?_⟩
  intro b hb
  change b ∈ (trunkPlanAt (trunkCatalog.states k) pi).cuts ++
    ((trunkParents (trunkCatalog.states k).context)[par]?.getD []) at hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hcuts b hb
  · exact hparent b hb

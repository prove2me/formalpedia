-- Prove2me | solution 1 for Freiman.trunk_goodness_from_specs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:30.327209+00:00
-- url     : https://prove2.me/submissions/77099ac6-4673-4add-a308-edb1a8bb1010

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_goodness_from_specs_from_order
import Theorems.Thm_Freiman_trunk_endpoint_strict_order

open Freiman

theorem solution (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    ∀ l ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels, lowerStrictGood (lowerChild p l) := by
  exact trunk_goodness_from_specs_from_order trunk_endpoint_strict_order p k pi par hm hs

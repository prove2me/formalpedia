-- Prove2me | solution 1 for Freiman.trunk_specs_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:30.343627+00:00
-- url     : https://prove2.me/submissions/bbe54003-ed02-46ea-8731-4f6820763908

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_specs_from_state
import Theorems.Thm_Freiman_trunk_endpoint_transfer
import Theorems.Thm_Freiman_trunk_endpoint_semantics
import Theorems.Thm_Freiman_trunk_greater_semantics
import Theorems.Thm_Freiman_trunk_catalog_sound

open Freiman

theorem solution (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par) :
    ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp := by
  exact trunk_specs_from_state trunk_endpoint_semantics trunk_greater_semantics
    (trunk_endpoint_transfer trunk_endpoint_semantics trunk_greater_semantics)
    p k pi par hm (trunk_catalog_sound k)

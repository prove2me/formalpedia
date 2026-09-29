-- Prove2me | solution 1 for Freiman.trunk_state_09_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:47.892372+00:00
-- url     : https://prove2.me/submissions/ab8dda41-c88d-4dca-98db-d07561979d9b

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_09
import Theorems.Thm_Freiman_trunk_bindings_09_000_100
import Theorems.Thm_Freiman_trunk_bindings_09_100_200
import Theorems.Thm_Freiman_trunk_bindings_09_200_260
import Theorems.Thm_Freiman_trunk_coverage_09

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 9).groups, trunkGroupValid trunkCatalog 9 g) ∧ trunkCoverage trunkCatalog 9 := by
  exact ⟨trunk_join_bindings_09 trunk_bindings_09_000_100 trunk_bindings_09_100_200 trunk_bindings_09_200_260,trunk_coverage_09⟩

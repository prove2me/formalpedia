-- Prove2me | solution 1 for Freiman.trunk_state_07_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:47.768794+00:00
-- url     : https://prove2.me/submissions/9b52e0e7-7ab6-44b9-a63a-8b691ce20428

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_07
import Theorems.Thm_Freiman_trunk_bindings_07_000_100
import Theorems.Thm_Freiman_trunk_bindings_07_100_200
import Theorems.Thm_Freiman_trunk_bindings_07_200_207
import Theorems.Thm_Freiman_trunk_coverage_07

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 7).groups, trunkGroupValid trunkCatalog 7 g) ∧ trunkCoverage trunkCatalog 7 := by
  exact ⟨trunk_join_bindings_07 trunk_bindings_07_000_100 trunk_bindings_07_100_200 trunk_bindings_07_200_207,trunk_coverage_07⟩

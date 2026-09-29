-- Prove2me | solution 1 for Freiman.trunk_state_03_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:29.11605+00:00
-- url     : https://prove2.me/submissions/09ef11c9-392c-4903-8af5-4176061c6596

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_03
import Theorems.Thm_Freiman_trunk_bindings_03_000_100
import Theorems.Thm_Freiman_trunk_bindings_03_100_200
import Theorems.Thm_Freiman_trunk_bindings_03_200_213
import Theorems.Thm_Freiman_trunk_coverage_03

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 3).groups, trunkGroupValid trunkCatalog 3 g) ∧ trunkCoverage trunkCatalog 3 := by
  exact ⟨trunk_join_bindings_03 trunk_bindings_03_000_100 trunk_bindings_03_100_200 trunk_bindings_03_200_213,trunk_coverage_03⟩

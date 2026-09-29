-- Prove2me | solution 1 for Freiman.trunk_state_04_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:28.810527+00:00
-- url     : https://prove2.me/submissions/6ebe7f55-8a54-4f6a-85a9-07853da3a2eb

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_04
import Theorems.Thm_Freiman_trunk_bindings_04_000_100
import Theorems.Thm_Freiman_trunk_bindings_04_100_200
import Theorems.Thm_Freiman_trunk_bindings_04_200_300
import Theorems.Thm_Freiman_trunk_bindings_04_300_400
import Theorems.Thm_Freiman_trunk_bindings_04_400_416
import Theorems.Thm_Freiman_trunk_coverage_04

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 4).groups, trunkGroupValid trunkCatalog 4 g) ∧ trunkCoverage trunkCatalog 4 := by
  exact ⟨trunk_join_bindings_04 trunk_bindings_04_000_100 trunk_bindings_04_100_200 trunk_bindings_04_200_300 trunk_bindings_04_300_400 trunk_bindings_04_400_416,trunk_coverage_04⟩

-- Prove2me | solution 1 for Freiman.trunk_state_13_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:29:02.210642+00:00
-- url     : https://prove2.me/submissions/36d53372-27c0-4c6c-8d2e-43a51e83bd06

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_13
import Theorems.Thm_Freiman_trunk_bindings_13_000_100
import Theorems.Thm_Freiman_trunk_bindings_13_100_173
import Theorems.Thm_Freiman_trunk_coverage_13

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 13).groups, trunkGroupValid trunkCatalog 13 g) ∧ trunkCoverage trunkCatalog 13 := by
  exact ⟨trunk_join_bindings_13 trunk_bindings_13_000_100 trunk_bindings_13_100_173,trunk_coverage_13⟩

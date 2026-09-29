-- Prove2me | solution 1 for Freiman.trunk_state_15_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:29:02.344243+00:00
-- url     : https://prove2.me/submissions/bf9c10a4-57ce-4b0f-b1cc-65008c45c148

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_15
import Theorems.Thm_Freiman_trunk_bindings_15_000_100
import Theorems.Thm_Freiman_trunk_bindings_15_100_110
import Theorems.Thm_Freiman_trunk_coverage_15

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 15).groups, trunkGroupValid trunkCatalog 15 g) ∧ trunkCoverage trunkCatalog 15 := by
  exact ⟨trunk_join_bindings_15 trunk_bindings_15_000_100 trunk_bindings_15_100_110,trunk_coverage_15⟩

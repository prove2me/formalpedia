-- Prove2me | solution 1 for Freiman.trunk_state_14_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:29:02.388347+00:00
-- url     : https://prove2.me/submissions/d8a67b34-0b26-429a-a88d-2c376b45a20c

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_14
import Theorems.Thm_Freiman_trunk_bindings_14_000_066
import Theorems.Thm_Freiman_trunk_coverage_14

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 14).groups, trunkGroupValid trunkCatalog 14 g) ∧ trunkCoverage trunkCatalog 14 := by
  exact ⟨trunk_join_bindings_14 trunk_bindings_14_000_066,trunk_coverage_14⟩

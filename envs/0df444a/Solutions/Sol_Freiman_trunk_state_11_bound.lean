-- Prove2me | solution 1 for Freiman.trunk_state_11_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:48.130491+00:00
-- url     : https://prove2.me/submissions/645e5b5f-73b5-48ba-a189-c2b60fb23cbe

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_11
import Theorems.Thm_Freiman_trunk_bindings_11_000_100
import Theorems.Thm_Freiman_trunk_bindings_11_100_121
import Theorems.Thm_Freiman_trunk_coverage_11

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 11).groups, trunkGroupValid trunkCatalog 11 g) ∧ trunkCoverage trunkCatalog 11 := by
  exact ⟨trunk_join_bindings_11 trunk_bindings_11_000_100 trunk_bindings_11_100_121,trunk_coverage_11⟩

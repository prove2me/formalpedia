-- Prove2me | solution 1 for Freiman.trunk_state_08_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:48.028302+00:00
-- url     : https://prove2.me/submissions/f45a6043-186a-473a-838b-1192a819fc1b

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_08
import Theorems.Thm_Freiman_trunk_bindings_08_000_100
import Theorems.Thm_Freiman_trunk_bindings_08_100_200
import Theorems.Thm_Freiman_trunk_bindings_08_200_262
import Theorems.Thm_Freiman_trunk_coverage_08

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 8).groups, trunkGroupValid trunkCatalog 8 g) ∧ trunkCoverage trunkCatalog 8 := by
  exact ⟨trunk_join_bindings_08 trunk_bindings_08_000_100 trunk_bindings_08_100_200 trunk_bindings_08_200_262,trunk_coverage_08⟩

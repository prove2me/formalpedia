-- Prove2me | solution 1 for Freiman.trunk_state_02_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:28.933053+00:00
-- url     : https://prove2.me/submissions/380d6888-0c7a-4106-bc6f-2edf18ddd051

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_02
import Theorems.Thm_Freiman_trunk_bindings_02_000_100
import Theorems.Thm_Freiman_trunk_bindings_02_100_184
import Theorems.Thm_Freiman_trunk_coverage_02

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 2).groups, trunkGroupValid trunkCatalog 2 g) ∧ trunkCoverage trunkCatalog 2 := by
  exact ⟨trunk_join_bindings_02 trunk_bindings_02_000_100 trunk_bindings_02_100_184,trunk_coverage_02⟩

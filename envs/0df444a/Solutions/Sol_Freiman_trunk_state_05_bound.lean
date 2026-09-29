-- Prove2me | solution 1 for Freiman.trunk_state_05_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:28.851579+00:00
-- url     : https://prove2.me/submissions/78462cb7-d51f-486c-990a-44470815fa45

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_05
import Theorems.Thm_Freiman_trunk_bindings_05_000_100
import Theorems.Thm_Freiman_trunk_bindings_05_100_200
import Theorems.Thm_Freiman_trunk_bindings_05_200_300
import Theorems.Thm_Freiman_trunk_bindings_05_300_400
import Theorems.Thm_Freiman_trunk_bindings_05_400_428
import Theorems.Thm_Freiman_trunk_coverage_05

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 5).groups, trunkGroupValid trunkCatalog 5 g) ∧ trunkCoverage trunkCatalog 5 := by
  exact ⟨trunk_join_bindings_05 trunk_bindings_05_000_100 trunk_bindings_05_100_200 trunk_bindings_05_200_300 trunk_bindings_05_300_400 trunk_bindings_05_400_428,trunk_coverage_05⟩

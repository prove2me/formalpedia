-- Prove2me | solution 1 for Freiman.trunk_state_00_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:09.802325+00:00
-- url     : https://prove2.me/submissions/be96c6b5-6687-440c-a71d-7a422e213e76

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_00
import Theorems.Thm_Freiman_trunk_bindings_00_000_100
import Theorems.Thm_Freiman_trunk_bindings_00_100_200
import Theorems.Thm_Freiman_trunk_bindings_00_200_300
import Theorems.Thm_Freiman_trunk_bindings_00_300_400
import Theorems.Thm_Freiman_trunk_bindings_00_400_438
import Theorems.Thm_Freiman_trunk_coverage_00

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 0).groups, trunkGroupValid trunkCatalog 0 g) ∧ trunkCoverage trunkCatalog 0 := by
  exact ⟨trunk_join_bindings_00 trunk_bindings_00_000_100 trunk_bindings_00_100_200 trunk_bindings_00_200_300 trunk_bindings_00_300_400 trunk_bindings_00_400_438,trunk_coverage_00⟩

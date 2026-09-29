-- Prove2me | solution 1 for Freiman.trunk_state_06_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:28.884047+00:00
-- url     : https://prove2.me/submissions/36541533-53c4-42fa-a253-61383a0483dc

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_06
import Theorems.Thm_Freiman_trunk_bindings_06_000_100
import Theorems.Thm_Freiman_trunk_bindings_06_100_185
import Theorems.Thm_Freiman_trunk_coverage_06

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 6).groups, trunkGroupValid trunkCatalog 6 g) ∧ trunkCoverage trunkCatalog 6 := by
  exact ⟨trunk_join_bindings_06 trunk_bindings_06_000_100 trunk_bindings_06_100_185,trunk_coverage_06⟩

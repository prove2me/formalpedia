-- Prove2me | solution 1 for Freiman.trunk_state_01_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:28.660894+00:00
-- url     : https://prove2.me/submissions/495a6969-f30f-4eec-ba53-65a9980d3813

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_join_bindings_01
import Theorems.Thm_Freiman_trunk_bindings_01_000_100
import Theorems.Thm_Freiman_trunk_bindings_01_100_200
import Theorems.Thm_Freiman_trunk_bindings_01_200_300
import Theorems.Thm_Freiman_trunk_bindings_01_300_400
import Theorems.Thm_Freiman_trunk_bindings_01_400_415
import Theorems.Thm_Freiman_trunk_coverage_01

open Freiman

theorem solution :
    (∀ g ∈ (trunkCatalog.states 1).groups, trunkGroupValid trunkCatalog 1 g) ∧ trunkCoverage trunkCatalog 1 := by
  exact ⟨trunk_join_bindings_01 trunk_bindings_01_000_100 trunk_bindings_01_100_200 trunk_bindings_01_200_300 trunk_bindings_01_300_400 trunk_bindings_01_400_415,trunk_coverage_01⟩

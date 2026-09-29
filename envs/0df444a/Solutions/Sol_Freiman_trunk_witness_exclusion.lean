-- Prove2me | solution 1 for Freiman.trunk_witness_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:37.730802+00:00
-- url     : https://prove2.me/submissions/a8e85af8-abbe-49ea-b040-5e68f0dcd371

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_normal_exclusion
import Theorems.Thm_Freiman_trunk_diagonal_exclusion

open Freiman

theorem solution (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) :
    TrunkWitnessExclusion C w := by
  by_cases hz : w.diagonal = 0
  · exact trunk_normal_exclusion C w hw hz
  · exact trunk_diagonal_exclusion C w hw hz

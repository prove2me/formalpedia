-- Prove2me | solution 1 for Freiman.trunk_all_bindings
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:29:02.241631+00:00
-- url     : https://prove2.me/submissions/ad7194f7-af05-4b2d-9e76-e2c751fa3f4d

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_state_00_bound
import Theorems.Thm_Freiman_trunk_state_01_bound
import Theorems.Thm_Freiman_trunk_state_02_bound
import Theorems.Thm_Freiman_trunk_state_03_bound
import Theorems.Thm_Freiman_trunk_state_04_bound
import Theorems.Thm_Freiman_trunk_state_05_bound
import Theorems.Thm_Freiman_trunk_state_06_bound
import Theorems.Thm_Freiman_trunk_state_07_bound
import Theorems.Thm_Freiman_trunk_state_08_bound
import Theorems.Thm_Freiman_trunk_state_09_bound
import Theorems.Thm_Freiman_trunk_state_10_bound
import Theorems.Thm_Freiman_trunk_state_11_bound
import Theorems.Thm_Freiman_trunk_state_12_bound
import Theorems.Thm_Freiman_trunk_state_13_bound
import Theorems.Thm_Freiman_trunk_state_14_bound
import Theorems.Thm_Freiman_trunk_state_15_bound

open Freiman

theorem solution :
    trunkAllBindings trunkCatalog := by
  intro k
  fin_cases k
  · exact trunk_state_00_bound
  · exact trunk_state_01_bound
  · exact trunk_state_02_bound
  · exact trunk_state_03_bound
  · exact trunk_state_04_bound
  · exact trunk_state_05_bound
  · exact trunk_state_06_bound
  · exact trunk_state_07_bound
  · exact trunk_state_08_bound
  · exact trunk_state_09_bound
  · exact trunk_state_10_bound
  · exact trunk_state_11_bound
  · exact trunk_state_12_bound
  · exact trunk_state_13_bound
  · exact trunk_state_14_bound
  · exact trunk_state_15_bound


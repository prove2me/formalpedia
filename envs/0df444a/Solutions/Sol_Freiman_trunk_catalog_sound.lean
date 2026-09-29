-- Prove2me | solution 1 for Freiman.trunk_catalog_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:40:30.129231+00:00
-- url     : https://prove2.me/submissions/cba37394-8a2c-47f1-a8cf-d5fab40fdedc

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_state_from_tree
import Theorems.Thm_Freiman_trunk_all_bindings
import Theorems.Thm_Freiman_trunk_tree_sound
import Theorems.Thm_Freiman_trunk_all_witnesses

open Freiman

theorem solution :
    ∀ k : Fin 16, trunkStateSound trunkCatalog k := by
  intro k
  exact trunk_state_from_tree trunkCatalog k (trunk_all_bindings k)
    (trunk_tree_sound trunkCatalog trunk_all_witnesses)

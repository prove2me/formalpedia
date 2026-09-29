-- Prove2me | solution 1 for Freiman.trunk_tree_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:28:09.541161+00:00
-- url     : https://prove2.me/submissions/c0915102-d42f-4436-b8b1-660347d6aaef

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_tree_induction
import Theorems.Thm_Freiman_trunk_witness_exclusion
import Theorems.Thm_Freiman_trunk_rectangle_split

open Freiman

theorem solution (C : TrunkCatalog) (hw : trunkAllWitnesses C) :
    TrunkTreeSound C := by
  exact trunk_tree_induction C hw (trunk_witness_exclusion C) trunk_rectangle_split

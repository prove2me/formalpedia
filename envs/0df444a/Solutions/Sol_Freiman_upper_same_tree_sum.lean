-- Prove2me | solution 1 for Freiman.upper_same_tree_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:35:50.745641+00:00
-- url     : https://prove2.me/submissions/308ad4f3-96ce-437b-ace6-fff8ad597360

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_normal_sum
import Theorems.Thm_Freiman_upper_derived_diagonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (T : List Bool → upperInterval) (hT : upperNormalTree T) (mT : upperMesh T) (hI : 0 < upperLength (T [])) :
    Set.Icc (2 * (T []).left) (2 * (T []).right) ⊆ upperSumSet (upperTreeSet T) (upperTreeSet T) := by
  rw [← upper_derived_diagonal (T []) hI]
  exact upper_normal_sum T T hT hT mT mT

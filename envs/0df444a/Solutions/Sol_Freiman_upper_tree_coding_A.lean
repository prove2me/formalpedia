-- Prove2me | solution 1 for Freiman.upper_tree_coding_A
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:36:15.910666+00:00
-- url     : https://prove2.me/submissions/f90433ac-66c4-4c17-8533-8f6525f17bac

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_digits_into_tree_A
import Theorems.Thm_Freiman_upper_tree_into_digits_A
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution  :
    upperTreeSet (upperTree [] 0) = upperKA := by
  exact Set.Subset.antisymm upper_tree_into_digits_A upper_digits_into_tree_A

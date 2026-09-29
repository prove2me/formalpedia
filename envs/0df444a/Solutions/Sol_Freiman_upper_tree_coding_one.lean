-- Prove2me | solution 1 for Freiman.upper_tree_coding_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:37:54.622276+00:00
-- url     : https://prove2.me/submissions/1fef1d16-6164-4533-b274-cdf6853d49b8

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_digits_into_tree_one
import Theorems.Thm_Freiman_upper_tree_into_digits_one
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution  :
    upperTreeSet (upperTree [1] 3) = upperKOne := by
  exact Set.Subset.antisymm upper_tree_into_digits_one upper_digits_into_tree_one

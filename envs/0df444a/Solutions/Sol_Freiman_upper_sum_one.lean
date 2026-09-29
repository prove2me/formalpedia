-- Prove2me | solution 1 for Freiman.upper_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:37:54.662362+00:00
-- url     : https://prove2.me/submissions/c907cd50-3d37-49c2-9d45-02de86176ab6

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_same_tree_sum
import Theorems.Thm_Freiman_upper_tree_normal
import Theorems.Thm_Freiman_upper_tree_mesh
import Theorems.Thm_Freiman_upper_tree_roots
import Theorems.Thm_Freiman_upper_tree_coding_one
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution  :
    Set.Icc (2 * upperTheta2) (2 * upperTheta1) ⊆ upperSumSet upperKOne upperKOne := by
  have h := upper_same_tree_sum (upperTree [1] 3) (upper_tree_normal _ _) (upper_tree_mesh _ _)
    upper_tree_roots.2.2.2
  rw [upper_tree_roots.2.1, upper_tree_coding_one] at h
  exact h

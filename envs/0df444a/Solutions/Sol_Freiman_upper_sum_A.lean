-- Prove2me | solution 1 for Freiman.upper_sum_A
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:36:15.925141+00:00
-- url     : https://prove2.me/submissions/5788131a-f848-4598-b481-061a891ec72e

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_same_tree_sum
import Theorems.Thm_Freiman_upper_tree_normal
import Theorems.Thm_Freiman_upper_tree_mesh
import Theorems.Thm_Freiman_upper_tree_roots
import Theorems.Thm_Freiman_upper_tree_coding_A
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution  :
    Set.Icc (2 * upperTheta8) (2 * upperTheta1) ⊆ upperSumSet upperKA upperKA := by
  have h := upper_same_tree_sum (upperTree [] 0) (upper_tree_normal _ _) (upper_tree_mesh _ _)
    upper_tree_roots.2.2.1
  rw [upper_tree_roots.1, upper_tree_coding_A] at h
  exact h

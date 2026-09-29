-- Prove2me | solution 1 for Freiman.upper_tree_mesh
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:36:15.871203+00:00
-- url     : https://prove2.me/submissions/3a67a4f7-d8f2-45e0-b914-4144ccb2cae8

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_tree_word_growth
import Theorems.Thm_Freiman_upper_tree_cylinder_width
import Theorems.Thm_Freiman_upper_mesh_from_prefix_bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (p : List ℕ+) (k : Fin 5) :
    upperMesh (upperTree p k) := by
  exact upper_mesh_from_prefix_bounds (upperTree p k)
    (fun w => (upperStateAt ⟨p, k⟩ w).word.length)
    (upper_tree_word_growth p k) (upper_tree_cylinder_width p k)

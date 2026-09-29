-- Prove2me | solution 1 for Freiman.upper_tree_normal
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:36:15.828886+00:00
-- url     : https://prove2.me/submissions/358bca44-8570-4b73-a0a0-029b3d8cb544

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_tree_split_identification
import Theorems.Thm_Freiman_upper_rows_normal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (p : List ℕ+) (k : Fin 5) :
    upperNormalTree (upperTree p k) := by
  intro w
  obtain ⟨hp, hl, hr⟩ := upper_tree_split_identification p k w
  rw [hp, hl, hr]
  exact upper_rows_normal _ _

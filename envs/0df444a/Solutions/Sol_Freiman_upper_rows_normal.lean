-- Prove2me | solution 1 for Freiman.upper_rows_normal
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:35:50.782932+00:00
-- url     : https://prove2.me/submissions/17a8e7cf-63ae-4784-990d-383bbdf1d791

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_row_normal_0
import Theorems.Thm_Freiman_upper_row_normal_1
import Theorems.Thm_Freiman_upper_row_normal_2
import Theorems.Thm_Freiman_upper_row_normal_3
import Theorems.Thm_Freiman_upper_row_normal_4
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (w : List ℕ+) (i : Fin 5) :
    let D := upperImageSplit w (upperRows i); upperNormalSplit D.parent D.left D.right := by
  fin_cases i
  · exact upper_row_normal_0 w
  · exact upper_row_normal_1 w
  · exact upper_row_normal_2 w
  · exact upper_row_normal_3 w
  · exact upper_row_normal_4 w

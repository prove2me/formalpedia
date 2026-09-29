-- Prove2me | solution 1 for Freiman.lowerJ_poly_checks
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:47.981271+00:00
-- url     : https://prove2.me/submissions/94f7242d-54a7-4c5e-a547-149d41a22bf3

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_poly_check_0
import Theorems.Thm_Freiman_lowerJ_poly_check_1
import Theorems.Thm_Freiman_lowerJ_poly_check_2
import Theorems.Thm_Freiman_lowerJ_poly_check_3

open Freiman

theorem solution (i : Fin 4) : lowerJPolyChecked i := by
  fin_cases i
  · exact Freiman.lowerJ_poly_check_0
  · exact Freiman.lowerJ_poly_check_1
  · exact Freiman.lowerJ_poly_check_2
  · exact Freiman.lowerJ_poly_check_3

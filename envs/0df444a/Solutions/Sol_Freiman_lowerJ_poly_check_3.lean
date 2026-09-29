-- Prove2me | solution 1 for Freiman.lowerJ_poly_check_3
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:21:37.023509+00:00
-- url     : https://prove2.me/submissions/89fda6dd-f518-4324-9517-f7a62ec11139

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem solution : lowerJPolyChecked 3 := by
  unfold lowerJPolyChecked
  constructor
  · funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel

#print axioms solution

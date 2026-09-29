-- Prove2me | solution 1 for Freiman.lowerJ_poly_check_0
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:06:15.849319+00:00
-- url     : https://prove2.me/submissions/1205b634-034f-4894-97ea-8a94c20c6639

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem solution : lowerJPolyChecked 0 := by
  unfold lowerJPolyChecked
  constructor
  · funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel

#print axioms solution

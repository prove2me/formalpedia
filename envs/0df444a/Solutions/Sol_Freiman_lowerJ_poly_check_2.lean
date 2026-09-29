-- Prove2me | solution 1 for Freiman.lowerJ_poly_check_2
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:21:35.585329+00:00
-- url     : https://prove2.me/submissions/d32eeb75-2e77-41f0-b805-84bdc339d46c

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem solution : lowerJPolyChecked 2 := by
  unfold lowerJPolyChecked
  constructor
  · funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel

#print axioms solution

-- Prove2me | solution 1 for Freiman.lowerJ_poly_check_1
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:10:44.126816+00:00
-- url     : https://prove2.me/submissions/99fba526-9ba9-498c-9dbe-2fa02cf1679e

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem solution : lowerJPolyChecked 1 := by
  unfold lowerJPolyChecked
  constructor
  · funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel

#print axioms solution

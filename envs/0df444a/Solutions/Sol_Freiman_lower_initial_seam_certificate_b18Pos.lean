-- Prove2me | solution 1 for Freiman.lower_initial_seam_certificate_b18Pos
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:55:52.689332+00:00
-- url     : https://prove2.me/submissions/823a7f71-199a-49b9-83db-67e0eb1de5d6

import Definitions.Def_Freiman_lowerInitialSeamData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem solution : lowerInitialSeamCertificateValid .b18Pos := by
  unfold lowerInitialSeamCertificateValid
  constructor
  · funext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

#print axioms solution

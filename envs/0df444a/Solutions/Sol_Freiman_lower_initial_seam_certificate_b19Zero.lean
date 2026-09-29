-- Prove2me | solution 1 for Freiman.lower_initial_seam_certificate_b19Zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:57:16.919637+00:00
-- url     : https://prove2.me/submissions/eb391737-13b3-4c7a-87bf-0bfa1edef70e

import Definitions.Def_Freiman_lowerInitialSeamData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem solution : lowerInitialSeamCertificateValid .b19Zero := by
  unfold lowerInitialSeamCertificateValid
  constructor
  · funext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

#print axioms solution

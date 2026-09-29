-- Prove2me | solution 1 for Freiman.lower_initial_seam_certificate_aZero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-10T12:54:37.317292+00:00
-- url     : https://prove2.me/submissions/96a7c434-6dee-49ff-a535-0791008e7d8a

import Definitions.Def_Freiman_lowerInitialSeamData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem solution : lowerInitialSeamCertificateValid .aZero := by
  unfold lowerInitialSeamCertificateValid
  constructor
  · funext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

#print axioms solution

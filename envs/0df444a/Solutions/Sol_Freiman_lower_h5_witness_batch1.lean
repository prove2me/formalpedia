-- Prove2me | solution 1 for Freiman.lower_h5_witness_batch1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T04:10:15.43751+00:00
-- url     : https://prove2.me/submissions/eaec3bf9-0d60-44b9-bfc5-6c0ccebd76fb

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance certRectangleValidDecidable (R : CertRectangle) :
    Decidable (certRectangleValid R) := by
  unfold certRectangleValid
  infer_instance

local instance certThresholdDataValidDecidable (t : CertThreshold) :
    Decidable (certThresholdDataValid t) := by
  unfold certThresholdDataValid
  infer_instance

local instance certCoefficientBoundValidDecidable (z : CertField) (q : ℚ) :
    Decidable (certCoefficientBoundValid z q) := by
  unfold certCoefficientBoundValid
  infer_instance

local instance certWitnessValidDecidable (w : CertWitness) :
    Decidable (certWitnessValid w) := by
  unfold certWitnessValid
  infer_instance

theorem solution (i : ℕ) (hlo : 1 ≤ i) (hhi : i ≤ 18) :
    certWitnessValid (lowerH5Witness i) := by
  interval_cases i <;> decide +kernel

-- Prove2me | solution 1 for Freiman.lower_h5_witness_batch3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T04:10:10.889727+00:00
-- url     : https://prove2.me/submissions/af374c79-40ae-4498-a30e-a516b15161ca

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

theorem solution (i : ℕ) (hlo : 37 ≤ i) (hhi : i ≤ 54) :
    certWitnessValid (lowerH5Witness i) := by
  interval_cases i <;> decide +kernel

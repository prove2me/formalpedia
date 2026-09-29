-- Prove2me | solution 1 for Freiman.cert_cross_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:59.472837+00:00
-- url     : https://prove2.me/submissions/ac965e98-90b3-46e4-95d7-e9a8aa40bd9d

import Theorems.Thm_Freiman_cert_cross_polynomial_from_field
import Theorems.Thm_Freiman_cert_field_add
import Theorems.Thm_Freiman_cert_field_sub
import Theorems.Thm_Freiman_cert_field_mul

open Freiman
open scoped BigOperators

theorem solution :
    ∀ (l u : CertThreshold) (r s : ℝ), certPolyEval (certCrossPolynomial l u) r s = certThresholdNum l s * certThresholdDen u r - certThresholdNum u s * certThresholdDen l r := by
  exact cert_cross_polynomial_from_field cert_field_add cert_field_sub cert_field_mul

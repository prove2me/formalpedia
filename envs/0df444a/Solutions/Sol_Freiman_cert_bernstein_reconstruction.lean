-- Prove2me | solution 1 for Freiman.cert_bernstein_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:59.438562+00:00
-- url     : https://prove2.me/submissions/67605ef9-cc02-4478-a651-1491cf2a421e

import Theorems.Thm_Freiman_cert_bernstein_reconstruction_from_field
import Theorems.Thm_Freiman_cert_field_add
import Theorems.Thm_Freiman_cert_field_scale

open Freiman
open scoped BigOperators

theorem solution :
    ∀ (P : CertPoly22) (R : CertRectangle), certRectangleValid R → ∀ r s : ℝ, certPolyEval P r s = certBernsteinEval (certBernsteinCoefficients P R) R r s := by
  exact cert_bernstein_reconstruction_from_field cert_field_add cert_field_scale

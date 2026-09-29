-- Prove2me | solution 1 for Freiman.cert_witness_polynomial_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:23.943917+00:00
-- url     : https://prove2.me/submissions/a4d14c7b-3b26-49ea-a5d1-0030fd96a452

import Theorems.Thm_Freiman_cert_bernstein_reconstruction
import Theorems.Thm_Freiman_cert_bernstein_nonnegative
import Theorems.Thm_Freiman_cert_witness_coefficients_nonnegative

open Freiman
open scoped BigOperators

theorem solution :
    ∀ w : CertWitness, certWitnessValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 ≤ certPolyEval (certCrossPolynomial w.lowerBound.threshold w.upperBound.threshold) r s := by
  intro w hw r s hm
  have hc := cert_witness_coefficients_nonnegative w hw
  rcases hw with ⟨_,_,hR,_,_,_,he,_,_⟩
  rw [cert_bernstein_reconstruction _ _ hR, ← he]
  exact cert_bernstein_nonnegative _ _ _ _ hR hm hc

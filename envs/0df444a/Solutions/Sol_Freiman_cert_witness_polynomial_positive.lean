-- Prove2me | solution 1 for Freiman.cert_witness_polynomial_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:23.970232+00:00
-- url     : https://prove2.me/submissions/fb05d510-0960-4fe9-9f44-84521be95364

import Theorems.Thm_Freiman_cert_bernstein_reconstruction
import Theorems.Thm_Freiman_cert_bernstein_positive
import Theorems.Thm_Freiman_cert_witness_coefficients_positive

open Freiman
open scoped BigOperators

theorem solution :
    ∀ w : CertWitness, certWitnessValid w → (∀ i j : Fin 3, 0 < w.lowerBounds i j) → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 < certPolyEval (certCrossPolynomial w.lowerBound.threshold w.upperBound.threshold) r s := by
  intro w hw hp r s hm
  have hc := cert_witness_coefficients_positive w hw hp
  rcases hw with ⟨_,_,hR,_,_,_,he,_,_⟩
  rw [cert_bernstein_reconstruction _ _ hR, ← he]
  exact cert_bernstein_positive _ _ _ _ hR hm hc

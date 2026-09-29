-- Prove2me | solution 1 for Freiman.cert_bernstein_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:11.336423+00:00
-- url     : https://prove2.me/submissions/d08cc925-dda0-48ee-9580-a5a6a3dfe410

import Theorems.Thm_Freiman_cert_bernstein_weights
import Theorems.Thm_Freiman_cert_weighted_positive

open Freiman
open scoped BigOperators

theorem solution :
    ∀ (C : CertPoly22) (R : CertRectangle) (r s : ℝ), certRectangleValid R → certRectangleMem R r s → (∀ i j : Fin 3, 0 < certFieldVal (C i j)) → 0 < certBernsteinEval C R r s := by
  intro C R r s hR hm hc
  have hw := cert_bernstein_weights R r s hR hm
  exact cert_weighted_positive (fun i j => certFieldVal (C i j)) (certBernsteinWeight R r s) hc hw.1 hw.2

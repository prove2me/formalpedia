-- Prove2me | solution 1 for Freiman.cert_witness_coefficients_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:11.142078+00:00
-- url     : https://prove2.me/submissions/104d9eff-95e2-4987-8d36-7b88c406e629

import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_coefficient_lower_positive

open Freiman
open scoped BigOperators

theorem solution :
    ∀ w : CertWitness, certWitnessValid w → (∀ i j : Fin 3, 0 < w.lowerBounds i j) → ∀ i j : Fin 3, 0 < certFieldVal (w.coefficients i j) := by
  intro w hw hp i j
  rcases hw with ⟨_,_,_,_,_,_,_,hb,_⟩
  have hq : 0 < (certFieldLower (w.coefficients i j):ℝ) := by
    exact_mod_cast cert_coefficient_lower_positive _ _ (hb i j) (hp i j)
  exact lt_of_lt_of_le hq (cert_field_lower_bound _)

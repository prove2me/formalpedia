-- Prove2me | solution 1 for Freiman.cert_witness_coefficients_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:11.032753+00:00
-- url     : https://prove2.me/submissions/df4fae75-c75c-4e80-963f-a15774039e8b

import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_coefficient_lower_nonnegative

open Freiman
open scoped BigOperators

theorem solution :
    ∀ w : CertWitness, certWitnessValid w → ∀ i j : Fin 3, 0 ≤ certFieldVal (w.coefficients i j) := by
  intro w hw i j
  rcases hw with ⟨_,_,_,_,_,_,_,hb,_⟩
  have hq : 0 ≤ (certFieldLower (w.coefficients i j):ℝ) := by
    exact_mod_cast cert_coefficient_lower_nonnegative _ _ (hb i j)
  exact le_trans hq (cert_field_lower_bound _)

-- Prove2me | solution 1 for Freiman.lower_initial_n_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:53.369799+00:00
-- url     : https://prove2.me/submissions/37942756-3aca-404b-9e46-9f43cd80a5e9

import Theorems.Thm_Freiman_lower_initial_period_ratio
import Theorems.Thm_Freiman_lower_initial_n_numerator_identity
import Theorems.Thm_Freiman_lower_initial_n_factorization
import Theorems.Thm_Freiman_lower_initial_n_certificates
import Theorems.Thm_Freiman_lower_initial_period_factor_positive
import Theorems.Thm_Freiman_lower_initial_n_quotient_positive
import Theorems.Thm_Freiman_cert_field_lower_bound
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialNCase) (n : ℕ) : 0 < lowerInitialNNumerator c (lowerInitialX n) := by
  have hx := lower_initial_period_ratio n
  rw [lower_initial_n_numerator_identity,lower_initial_n_factorization c (lower_initial_n_certificates c)]
  exact mul_pos (lower_initial_period_factor_positive _ hx.1 hx.2.1)
    (lower_initial_n_quotient_positive cert_field_lower_bound c (lower_initial_n_certificates c) _ ⟨hx.1,hx.2.2⟩)

-- Prove2me | solution 1 for Freiman.cert_radical_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:47.295933+00:00
-- url     : https://prove2.me/submissions/2b219487-72c2-4757-8818-e2a4eb6db029

import Theorems.Thm_Freiman_cert_sqrt_bracket
import Theorems.Thm_Freiman_cert_radical_square_certificates

open Freiman
open scoped BigOperators

theorem solution :
    ((certSqrt3Lower:ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < certSqrt3Upper) ∧
    ((certSqrt7Lower:ℝ) < Real.sqrt 7 ∧ Real.sqrt 7 < certSqrt7Upper) ∧
    ((certSqrt21Lower:ℝ) < Real.sqrt 21 ∧ Real.sqrt 21 < certSqrt21Upper) := by
  obtain ⟨h3,h7,h21⟩ := cert_radical_square_certificates
  exact ⟨cert_sqrt_bracket _ _ _ h3.1 h3.2.1 h3.2.2.1 h3.2.2.2,
    cert_sqrt_bracket _ _ _ h7.1 h7.2.1 h7.2.2.1 h7.2.2.2,
    cert_sqrt_bracket _ _ _ h21.1 h21.2.1 h21.2.2.1 h21.2.2.2⟩

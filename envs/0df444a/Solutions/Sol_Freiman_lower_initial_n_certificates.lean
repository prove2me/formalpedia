-- Prove2me | solution 1 for Freiman.lower_initial_n_certificates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:53.307885+00:00
-- url     : https://prove2.me/submissions/672e8ad7-7005-408b-bf50-6702a1633d31

import Theorems.Thm_Freiman_lower_initial_n_certificate_n13
import Theorems.Thm_Freiman_lower_initial_n_certificate_n14
import Theorems.Thm_Freiman_lower_initial_n_certificate_aux
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution : ∀ c : LowerInitialNCase, lowerInitialNCertificateValid c := by
  intro c
  cases c
  · exact lower_initial_n_certificate_n13
  · exact lower_initial_n_certificate_n14
  · exact lower_initial_n_certificate_aux

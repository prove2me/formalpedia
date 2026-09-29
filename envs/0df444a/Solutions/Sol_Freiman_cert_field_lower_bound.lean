-- Prove2me | solution 1 for Freiman.cert_field_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:03.370813+00:00
-- url     : https://prove2.me/submissions/98cf68cd-ed3e-47f6-882d-161b81c50537

import Theorems.Thm_Freiman_cert_radical_enclosures
import Theorems.Thm_Freiman_cert_directed_term_bound

open Freiman
open scoped BigOperators

theorem solution :
    ∀ z : CertField, (certFieldLower z:ℝ) ≤ certFieldVal z := by
  intro z
  obtain ⟨h3,h7,h21⟩ := cert_radical_enclosures
  have hb := cert_directed_term_bound z.b certSqrt3Lower certSqrt3Upper (Real.sqrt 3) h3.1.le h3.2.le
  have hc := cert_directed_term_bound z.c certSqrt7Lower certSqrt7Upper (Real.sqrt 7) h7.1.le h7.2.le
  have hd := cert_directed_term_bound z.d certSqrt21Lower certSqrt21Upper (Real.sqrt 21) h21.1.le h21.2.le
  simp only [certFieldLower, certFieldVal, Rat.cast_add]
  exact add_le_add (add_le_add (add_le_add le_rfl hb) hc) hd

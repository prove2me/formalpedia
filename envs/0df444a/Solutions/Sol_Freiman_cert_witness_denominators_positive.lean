-- Prove2me | solution 1 for Freiman.cert_witness_denominators_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:24.125586+00:00
-- url     : https://prove2.me/submissions/730e5d07-3005-4a5a-ab83-96baf6a62424

import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_threshold_denominator_positive

open Freiman
open scoped BigOperators

theorem solution :
    ∀ (w : CertWitness), certWitnessValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 < certThresholdDen w.lowerBound.threshold r ∧ 0 < certThresholdDen w.upperBound.threshold r := by
  intro w hw r s hm
  rcases hw with ⟨_,_,_,hr0,hL,hU,_,_,_⟩
  have hr0' : (0:ℝ) ≤ w.rectangle.r0 := by exact_mod_cast hr0
  have hr : 0 ≤ r := le_trans hr0' hm.1
  have hx : ∀ z : CertField, 0 ≤ certFieldLower z → 0 ≤ certFieldVal z := by
    intro z hz
    have hz' : (0:ℝ) ≤ (certFieldLower z:ℝ) := by exact_mod_cast hz
    exact le_trans hz' (cert_field_lower_bound z)
  exact ⟨cert_threshold_denominator_positive _ _ hr (hx _ hL.1) (hx _ hL.2),
    cert_threshold_denominator_positive _ _ hr (hx _ hU.1) (hx _ hU.2)⟩

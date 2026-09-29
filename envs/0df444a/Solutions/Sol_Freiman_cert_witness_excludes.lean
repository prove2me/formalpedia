-- Prove2me | solution 1 for Freiman.cert_witness_excludes
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:23.766973+00:00
-- url     : https://prove2.me/submissions/ddf102fc-81a2-49cb-b365-9b146262c7da

import Theorems.Thm_Freiman_cert_witness_denominators_positive
import Theorems.Thm_Freiman_cert_witness_polynomial_nonnegative
import Theorems.Thm_Freiman_cert_witness_polynomial_positive
import Theorems.Thm_Freiman_cert_cross_polynomial
import Theorems.Thm_Freiman_cert_threshold_cross_order
import Theorems.Thm_Freiman_cert_bound_pair_incompatible

open Freiman
open scoped BigOperators

theorem solution :
    ∀ (w : CertWitness), certWitnessValid w → ∀ r s q : ℝ, certRectangleMem w.rectangle r s → ¬ (certBoundHolds w.lowerBound r s q ∧ certBoundHolds w.upperBound r s q) := by
  intro w hw r s q hm
  have hd := cert_witness_denominators_positive w hw r s hm
  have ho := cert_threshold_cross_order _ _ r s hd.1 hd.2
  have he := cert_cross_polynomial w.lowerBound.threshold w.upperBound.threshold r s
  have hl := hw.1
  have hu := hw.2.1
  have hsign := hw.2.2.2.2.2.2.2.2
  apply cert_bound_pair_incompatible _ _ r s q hl hu
  rcases hsign with hp | hs
  · have hpos := cert_witness_polynomial_positive w hw hp r s hm
    rw [he] at hpos
    exact Or.inl (ho.2.mp hpos)
  · have hnonneg := cert_witness_polynomial_nonnegative w hw r s hm
    rw [he] at hnonneg
    exact Or.inr ⟨ho.1.mp hnonneg,hs⟩

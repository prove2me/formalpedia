-- Prove2me | solution 2 for FamousTheorems.ruzsa_covering_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:57:38.893562+00:00
-- url     : https://prove2.me/submissions/374d7f6f-1d71-4a57-9247-aa7d36233232

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [AddGroup G] [DecidableEq G] {A B : Finset G} {K : ℝ} (hB : B.Nonempty)
    (hK : ((A + B).card : ℝ) ≤ K * B.card) : ∃ F ⊆ A, (F.card : ℝ) ≤ K ∧ A ⊆ F + (B - B) := by
  exact Finset.ruzsa_covering_add hB hK

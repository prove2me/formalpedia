-- Prove2me | solution 3 for FamousTheorems.ruzsa_covering_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:58:01.134529+00:00
-- url     : https://prove2.me/submissions/36b74c2b-fa5e-4a58-aa1e-18b9df9ff2ec

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [AddGroup G] [DecidableEq G] {A B : Finset G} {K : ℝ} (hB : B.Nonempty)
    (hK : ((A + B).card : ℝ) ≤ K * B.card) : ∃ F ⊆ A, (F.card : ℝ) ≤ K ∧ A ⊆ F + (B - B) :=
  Finset.ruzsa_covering_add hB hK

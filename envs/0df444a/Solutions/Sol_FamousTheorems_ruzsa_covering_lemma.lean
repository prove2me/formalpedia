-- Prove2me | solution 1 for FamousTheorems.ruzsa_covering_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:57:05.630361+00:00
-- url     : https://prove2.me/submissions/db74882a-9390-4c54-ad32-fd17e597dec3

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [AddGroup G] [DecidableEq G] {A B : Finset G} {K : ℝ} (hB : B.Nonempty)
    (hK : ((A + B).card : ℝ) ≤ K * B.card) : ∃ F ⊆ A, (F.card : ℝ) ≤ K ∧ A ⊆ F + (B - B) :=
  Finset.ruzsa_covering_add hB hK

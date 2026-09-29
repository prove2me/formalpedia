-- Prove2me | solution 1 for FamousTheorems.godel_beta_function_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:08:02.55099+00:00
-- url     : https://prove2.me/submissions/2042aaa3-d2f6-4c40-9afe-0a8509fcef80

import Mathlib

theorem solution (l : List ℕ) :
    ∃ n : ℕ, ∀ i : Fin l.length, Nat.beta n i = l[i] :=
  ⟨Nat.unbeta l, Nat.beta_unbeta_coe l⟩

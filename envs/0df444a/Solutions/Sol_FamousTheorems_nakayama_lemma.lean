-- Prove2me | solution 1 for FamousTheorems.nakayama_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:07:59.872379+00:00
-- url     : https://prove2.me/submissions/57a595d7-b6ca-4525-898b-f2733647f71a

import Mathlib

theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M)
    (hN : N.FG) (hIN : N ≤ I • N) (hIjac : I ≤ (⊥ : Ideal R).jacobson) : N = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I N hN hIN hIjac

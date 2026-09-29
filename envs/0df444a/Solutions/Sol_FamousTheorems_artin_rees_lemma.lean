-- Prove2me | solution 1 for FamousTheorems.artin_rees_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:31:13.801222+00:00
-- url     : https://prove2.me/submissions/e0ba4400-bb55-4d8f-9072-f34122ad0045

import Mathlib

theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) :
    ∃ k : ℕ, ∀ n ≥ k, I ^ n • (⊤ : Submodule R M) ⊓ N = I ^ (n - k) • (I ^ k • (⊤ : Submodule R M) ⊓ N) :=
  Ideal.exists_pow_inf_eq_pow_smul I N

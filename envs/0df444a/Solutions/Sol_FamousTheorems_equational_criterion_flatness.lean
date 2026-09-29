-- Prove2me | solution 1 for FamousTheorems.equational_criterion_flatness
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:47:11.695668+00:00
-- url     : https://prove2.me/submissions/56537bd6-b947-491c-a81f-9d57d28b0142

import Mathlib

theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ {l : ℕ} {f : Fin l →₀ R} {x : (Fin l →₀ R) →ₗ[R] M}, x f = 0 →
        ∃ (k : ℕ) (a : (Fin l →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M), x = y ∘ₗ a ∧ a f = 0 :=
  Module.Flat.iff_forall_exists_factorization

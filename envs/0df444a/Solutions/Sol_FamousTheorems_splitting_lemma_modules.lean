-- Prove2me | solution 1 for FamousTheorems.splitting_lemma_modules
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:13:15.059749+00:00
-- url     : https://prove2.me/submissions/a249f131-6a1f-4502-b5ef-9dbd337bf9ee

import Mathlib

theorem solution {R M N P : Type*} [Semiring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M]
    [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [∃ l : P →ₗ[R] N, g ∘ₗ l = LinearMap.id, ∃ l : N →ₗ[R] M, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm.toLinearMap ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e.toLinearMap] :=
  h.split_tfae hf hg

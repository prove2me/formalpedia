-- Prove2me | solution 1 for FamousTheorems.orzech_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:46:59.841168+00:00
-- url     : https://prove2.me/submissions/ec5a5096-f772-4e3b-8900-f04baedb5093

import Mathlib

theorem solution {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [IsNoetherian R M]
    (i f : N →ₗ[R] M) (hi : Function.Injective i) (hf : Function.Surjective f) : Function.Injective f :=
  IsNoetherian.injective_of_surjective_of_injective i f hi hf

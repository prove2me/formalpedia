-- Prove2me | solution 1 for FamousTheorems.first_isomorphism_theorem_rings
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:34:11.609157+00:00
-- url     : https://prove2.me/submissions/2b2c6983-4d6d-4b14-9d7b-e21557b623cc

import Mathlib

theorem solution {R S : Type*} [Ring R] [Semiring S] (f : R →+* S) (hf : Function.Surjective f) :
    Nonempty (R ⧸ RingHom.ker f ≃+* S) :=
  ⟨RingHom.quotientKerEquivOfSurjective hf⟩

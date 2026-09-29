-- Prove2me | solution 2 for FamousTheorems.first_isomorphism_theorem_rings
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:34:43.173902+00:00
-- url     : https://prove2.me/submissions/2317db97-d053-4a17-983a-07ea2608eaa6

import Mathlib

theorem solution {R S : Type*} [Ring R] [Semiring S] (f : R →+* S) (hf : Function.Surjective f) :
    Nonempty (R ⧸ RingHom.ker f ≃+* S) :=
  ⟨RingHom.quotientKerEquivOfSurjective hf⟩

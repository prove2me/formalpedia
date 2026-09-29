-- Prove2me | solution 1 for FamousTheorems.jacobson_density
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:18:50.668138+00:00
-- url     : https://prove2.me/submissions/987be323-61c4-4f44-92e9-7ee1409b9c98

import Mathlib

theorem solution {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    (f : Module.End (Module.End R M) M) (s : Finset M) : ∃ r : R, ∀ m ∈ s, f m = r • m :=
  _root_.jacobson_density f s

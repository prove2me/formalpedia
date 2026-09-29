-- Prove2me | solution 1 for FamousTheorems.engel_theorem_lie
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:03:51.57988+00:00
-- url     : https://prove2.me/submissions/e9c67861-7292-4148-92d6-0ca4ef467c6f

import Mathlib

theorem solution {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsNoetherian R L] :
    LieRing.IsNilpotent L ↔ ∀ x : L, IsNilpotent (LieAlgebra.ad R L x) :=
  LieAlgebra.isNilpotent_iff_forall

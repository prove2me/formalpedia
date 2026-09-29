-- Prove2me | solution 1 for FamousTheorems.cartan_criterion_semisimplicity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:17:22.64772+00:00
-- url     : https://prove2.me/submissions/1cbafa9e-4842-4f65-84ed-22a700c31234

import Mathlib

theorem solution (R L : Type*) [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L] [IsNoetherian R L]
    [Module.Free R L] [LieAlgebra.HasTrivialRadical R L] : LieAlgebra.IsKilling R L :=
  inferInstance

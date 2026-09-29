-- Prove2me | solution 1 for FamousTheorems.cartan_criterion_solvability
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:14:53.950609+00:00
-- url     : https://prove2.me/submissions/fbd2633b-fc98-4946-b0aa-9f518c6350a5

import Mathlib

theorem solution {R L : Type*} [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L] [IsNoetherian R L]
    [Module.Free R L] (h : ∀ x y : L, y ∈ LieAlgebra.derivedSeries R L 1 → killingForm R L x y = 0) :
    LieAlgebra.IsSolvable L :=
  LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero h

-- Prove2me | solution 1 for FamousTheorems.hermite_finiteness_number_fields
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:27:05.506007+00:00
-- url     : https://prove2.me/submissions/fe4d560d-6013-4216-806e-abb808a8bfe6

import Mathlib

theorem solution (A : Type*) [Field A] [CharZero A] (N : ℕ) :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F } |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |NumberField.discr K| ≤ N}.Finite :=
  NumberField.finite_of_discr_bdd A N

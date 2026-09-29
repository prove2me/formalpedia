-- Prove2me | solution 1 for FamousTheorems.algebraic_elements_countable_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:11:06.654882+00:00
-- url     : https://prove2.me/submissions/a3983778-b0e5-4095-b454-2f6aec784794

import Mathlib

theorem solution (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
    [Module.IsTorsionFree R A] [Countable R] [CharZero A] :
    Cardinal.mk { x : A // IsAlgebraic R x } = Cardinal.aleph0 :=
  Algebraic.cardinalMk_of_countable_of_charZero R A

-- Prove2me | solution 1 for FamousTheorems.algebraic_over_algebraic_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:03:36.16789+00:00
-- url     : https://prove2.me/submissions/9c518ba0-e1b4-491a-aa94-518807d41219

import Mathlib

theorem solution (R S A : Type*) [CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [NoZeroDivisors S] [Algebra.IsAlgebraic R S] [Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  Algebra.IsAlgebraic.trans R S A

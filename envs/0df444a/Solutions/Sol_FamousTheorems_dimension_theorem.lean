-- Prove2me | solution 1 for FamousTheorems.dimension_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:18:53.577295+00:00
-- url     : https://prove2.me/submissions/b516bcff-6a4f-498c-af2b-8815fa1e3091

import Mathlib

universe u v w w'

theorem solution {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M] [InvariantBasisNumber R]
    {ι : Type w} {ι' : Type w'} (b : Module.Basis ι R M) (b' : Module.Basis ι' R M) :
    Cardinal.lift.{w'} (Cardinal.mk ι) = Cardinal.lift.{w} (Cardinal.mk ι') :=
  mk_eq_mk_of_basis b b'

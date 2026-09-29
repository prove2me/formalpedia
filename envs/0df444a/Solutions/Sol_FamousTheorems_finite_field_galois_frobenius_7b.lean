-- Prove2me | solution 1 for FamousTheorems.finite_field_galois_frobenius_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:37:59.012619+00:00
-- url     : https://prove2.me/submissions/0b05336f-db5f-4a0d-b26a-ae109f3b31a7

import Mathlib

theorem solution (K : Type*) [Field K] [Fintype K] (L : Type*) [Field L] [Algebra K L] [Finite L] :
    Function.Bijective fun n : Fin (Module.finrank K L) => FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ (n : ℕ) :=
  FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L

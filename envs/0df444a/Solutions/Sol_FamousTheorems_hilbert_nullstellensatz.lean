-- Prove2me | solution 1 for FamousTheorems.hilbert_nullstellensatz
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:06:02.708481+00:00
-- url     : https://prove2.me/submissions/22f54720-dec8-4cff-bbd8-62c4177120d9

import Mathlib

theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] {σ : Type*} [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K I) = I.radical :=
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

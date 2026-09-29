-- Prove2me | solution 1 for FamousTheorems.quadratic_forms_alg_closed
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:29:37.463802+00:00
-- url     : https://prove2.me/submissions/e27bd444-0c4f-47a2-9598-89598aa31767

import Mathlib

theorem solution {K M : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q : QuadraticForm K M) (hQ : (QuadraticMap.associated Q).SeparatingLeft) :
    QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K (1 : Fin (Module.finrank K M) → K)) :=
  QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed Q hQ

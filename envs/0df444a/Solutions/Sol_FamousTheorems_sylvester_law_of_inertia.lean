-- Prove2me | solution 1 for FamousTheorems.sylvester_law_of_inertia
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:27:45.321852+00:00
-- url     : https://prove2.me/submissions/0ecb4123-5628-4ff7-a4f5-5ed5729ed5f1

import Mathlib

theorem solution {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (Module.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w) :=
  QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared Q

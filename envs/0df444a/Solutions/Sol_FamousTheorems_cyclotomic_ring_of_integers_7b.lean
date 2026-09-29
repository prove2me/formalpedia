-- Prove2me | solution 1 for FamousTheorems.cyclotomic_ring_of_integers_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:39:01.167001+00:00
-- url     : https://prove2.me/submissions/08e7ee27-4b9b-44b9-9fee-db9ec730c19c

import Mathlib

theorem solution {n : ℕ} [NeZero n] {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {n} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : IsIntegralClosure (Algebra.adjoin ℤ ({ζ} : Set K)) ℤ K :=
  IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ

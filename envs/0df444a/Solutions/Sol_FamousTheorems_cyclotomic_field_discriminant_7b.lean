-- Prove2me | solution 1 for FamousTheorems.cyclotomic_field_discriminant_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:42:43.299229+00:00
-- url     : https://prove2.me/submissions/093a1d6b-ed50-4f04-aafd-3d68f1719d30

import Mathlib

theorem solution (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    NumberField.discr K = (-1) ^ (n.totient / 2) *
      ((n : ℤ) ^ n.totient / ((∏ p ∈ n.primeFactors, p ^ (n.totient / (p - 1)) : ℕ) : ℤ)) :=
  IsCyclotomicExtension.Rat.discr n K

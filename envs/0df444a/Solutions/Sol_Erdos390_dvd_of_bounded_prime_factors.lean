-- Prove2me | solution 1 for Erdos390.dvd_of_bounded_prime_factors
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-06T05:21:13.618753+00:00
-- url     : https://prove2.me/submissions/82dc4690-a50f-4a8c-bad1-9cfc726f637f

import Mathlib

theorem solution
    {D P B : ℕ} (hD : D ≠ 0) (hP : P ≠ 0)
    (hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ D → ℓ ≤ B)
    (hval : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ B → D.factorization ℓ ≤ P.factorization ℓ) :
    D ∣ P := by
  rw [← Nat.factorization_le_iff_dvd hD hP]
  intro ℓ
  by_cases hℓ : ℓ.Prime
  · by_cases hdvd : ℓ ∣ D
    · exact hval ℓ hℓ (hprime ℓ hℓ hdvd)
    · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hℓ]
    exact Nat.zero_le _

-- Prove2me | solution 1 for Erdos287.mixed_residue_divisor_moment
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:05:21.764801+00:00
-- url     : https://prove2.me/submissions/403bb21a-8eb5-418e-a16c-44463ca0bd1e

import Mathlib

open Finset

set_option autoImplicit false

/-- A finite menu of local residues bounds all compatible squarefree moduli. -/
theorem solution (k : ℕ) (c : Fin k → ℤ) (C A y : ℤ)
    (hy : ∀ i, C * y ≠ c i) (Q : Finset ℕ)
    (hsq : ∀ q ∈ Q, Squarefree q)
    (hmenu : ∀ q ∈ Q, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i, (p : ℤ) ∣ C * A - c i)
    (hres : ∀ q ∈ Q, (q : ℤ) ∣ y - A)
    (B : ℕ) :
    (∑ q ∈ Q, q.divisors.card ^ B) ≤
      (∏ i : Fin k, (C * y - c i)).natAbs.divisors.card ^ (B + 1) := by
  classical
  let P := ∏ i : Fin k, (C * y - c i)
  have hP : P ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hy i))
  have hP₀ : P.natAbs ≠ 0 := by simpa using hP
  have hdiv (q : ℕ) (hq : q ∈ Q) : q ∣ P.natAbs := by
    apply Int.natCast_dvd.mp
    have hprod := congrArg (fun n : ℕ => (n : ℤ))
      (Nat.prod_primeFactors_of_squarefree (hsq q hq))
    simp only [Nat.cast_prod] at hprod
    rw [← hprod]
    apply Finset.prod_dvd_of_coprime
    · intro p hp r hr hpr
      exact Nat.isCoprime_iff_coprime.mpr
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hr)).mpr hpr)
    · intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hpq := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨i, hi⟩ := hmenu q hq p hprime hpq
      have hpy : (p : ℤ) ∣ y - A :=
        (Int.natCast_dvd_natCast.mpr hpq).trans (hres q hq)
      have hpi : (p : ℤ) ∣ C * y - c i := by
        have heq : C * y - c i = (C * A - c i) + C * (y - A) := by ring
        rw [heq]
        exact hi.add (dvd_mul_of_dvd_right hpy C)
      exact hpi.trans (dvd_prod_of_mem (fun j : Fin k => C * y - c j) (mem_univ i))
  have hsub : Q ⊆ P.natAbs.divisors := fun q hq => Nat.mem_divisors.mpr ⟨hdiv q hq, hP₀⟩
  calc
    _ ≤ ∑ _ ∈ Q, P.natAbs.divisors.card ^ B := by
      apply sum_le_sum
      intro q hq
      exact Nat.pow_le_pow_left (card_le_card (Nat.divisors_subset_of_dvd hP₀ (hdiv q hq))) _
    _ = Q.card * P.natAbs.divisors.card ^ B := by simp
    _ ≤ P.natAbs.divisors.card * P.natAbs.divisors.card ^ B :=
      Nat.mul_le_mul_right _ (card_le_card hsub)
    _ = _ := by rw [pow_succ', mul_comm]


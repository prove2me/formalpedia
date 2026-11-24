-- Prove2me | solution 1 for Dubner.goldbach_of_conjecture_4a
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-24T11:36:15.838566+00:00
-- url     : https://prove2.me/submissions/d61c9527-78ca-478e-86a3-36ae06457079

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

open Dubner

namespace DubnerGoldbachCheck

/-- Trial division from `d` upwards, with `fuel` steps. It returns `true` only when it reaches a `d`
with `n < d * d` without having met a divisor of `n`. -/
def trial (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 =>
    if n < d * d then true
    else if n % d = 0 then false
    else trial n (d + 1) fuel

/-- A primality test by trial division, written by structural recursion so that the kernel can
evaluate it. -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && trial n 2 n

theorem prime_of_trial (n : ℕ) (hn : 2 ≤ n) :
    ∀ (fuel d : ℕ), (∀ m : ℕ, 2 ≤ m → m < d → ¬ m ∣ n) → trial n d fuel = true → Nat.Prime n := by
  intro fuel
  induction fuel with
  | zero =>
    intro d _ h
    simp [trial] at h
  | succ fuel ih =>
    intro d hd h
    unfold trial at h
    split_ifs at h with h1 h2
    · -- `n < d * d`: no divisor up to the square root
      rw [Nat.prime_def_le_sqrt]
      refine ⟨hn, fun m hm2 hmsq => hd m hm2 ?_⟩
      have hmm : m * m ≤ n := Nat.le_sqrt.mp hmsq
      by_contra hlt
      have hdm : d ≤ m := Nat.le_of_not_lt hlt
      have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · -- `d` does not divide `n`: go on with `d + 1`
      refine ih (d + 1) (fun m hm2 hmlt => ?_) h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmlt with hlt | rfl
      · exact hd m hm2 hlt
      · intro hdvd
        exact h2 (Nat.mod_eq_zero_of_dvd hdvd)

theorem prime_of_isPrimeB {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  unfold isPrimeB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h2, ht⟩ := h
  have hn : 2 ≤ n := of_decide_eq_true h2
  exact prime_of_trial n hn n 2 (fun m hm2 hmlt => absurd hm2 (by omega)) ht

/-- The finite part: every even number `2 * k + 4` with `k < 2103`, that is every even number from
`4` to `4208`, is `p + (n - p)` with both terms prime and `p < 104`. -/
theorem finite_check :
    ∀ k < 2103, ∃ p < 104, p ≤ 2 * k + 4 ∧ isPrimeB p = true ∧ isPrimeB (2 * k + 4 - p) = true := by
  decide +kernel

end DubnerGoldbachCheck

open DubnerGoldbachCheck in
/-- Dubner's Conjecture 4a implies Goldbach's conjecture.

Above `4208` the two t-primes given by Conjecture 4a are primes. From `4` to `4208` a pair of primes
is found by the finite check above. -/
theorem solution
    (h4a : ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q) :
    ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro n hn2 hne
  by_cases hbig : 4208 < n
  · obtain ⟨p, q, hp, hq, hpq⟩ := h4a n hbig hne
    exact ⟨p, q, hp.1, hq.1, hpq⟩
  · obtain ⟨j, hj⟩ := hne
    -- `n = j + j` with `2 ≤ j ≤ 2104`; write `n = 2 * (j - 2) + 4`
    have hk : j - 2 < 2103 := by omega
    obtain ⟨p, _, hple, hp, hq⟩ := finite_check (j - 2) hk
    have hn' : 2 * (j - 2) + 4 = n := by omega
    rw [hn'] at hple hq
    exact ⟨p, n - p, prime_of_isPrimeB hp, prime_of_isPrimeB hq, by omega⟩

-- Prove2me | solution 1 for Dubner.conjecture_4a_of_conjecture_3a
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-24T11:17:29.175518+00:00
-- url     : https://prove2.me/submissions/6667ca33-e735-46a3-9683-d55d5b95b2f5

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

open Dubner

namespace DubnerReduction

/-- A middle number is at least `3`, because `m - 1` is prime. -/
theorem three_le_of_isMiddleNumber {m : ℕ} (hm : IsMiddleNumber m) : 3 ≤ m := by
  have h2 : 2 ≤ m - 1 := hm.1.two_le
  omega

/-- The upper neighbour of a middle number is a t-prime: its twin is `m - 1`. -/
theorem isTPrime_succ {m : ℕ} (hm : IsMiddleNumber m) : IsTPrime (m + 1) := by
  have h3 := three_le_of_isMiddleNumber hm
  refine ⟨hm.2, Or.inl ?_⟩
  have h : m + 1 - 2 = m - 1 := by omega
  rw [h]
  exact hm.1

/-- The lower neighbour of a middle number is a t-prime: its twin is `m + 1`. -/
theorem isTPrime_pred {m : ℕ} (hm : IsMiddleNumber m) : IsTPrime (m - 1) := by
  have h3 := three_le_of_isMiddleNumber hm
  refine ⟨hm.1, Or.inr ?_⟩
  have h : m - 1 + 2 = m + 1 := by omega
  rw [h]
  exact hm.2

end DubnerReduction

open DubnerReduction in
/-- Dubner's Conjecture 3a implies his Conjecture 4a.

An even `n > 4208` is `N`, `N + 2` or `N - 2` for a multiple `N > 4206` of `6`. Writing
`N = m₁ + m₂` with middle numbers, Dubner's three identities
`N = (m₁ + 1) + (m₂ - 1)`, `N + 2 = (m₁ + 1) + (m₂ + 1)`, `N - 2 = (m₁ - 1) + (m₂ - 1)`
express `n` as a sum of two t-primes. -/
theorem solution
    (h3a : ∀ N : ℕ, 6 ∣ N → 4206 < N →
      ∃ m₁ m₂ : ℕ, IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂) :
    ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q := by
  intro n hn hne
  obtain ⟨j, hj⟩ := hne
  have hmod : n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4 := by omega
  rcases hmod with h0 | h2 | h4
  · -- `n = N`
    obtain ⟨m₁, m₂, h₁, h₂, hN⟩ := h3a n (Nat.dvd_of_mod_eq_zero h0) (by omega)
    have h3 := three_le_of_isMiddleNumber h₂
    exact ⟨m₁ + 1, m₂ - 1, isTPrime_succ h₁, isTPrime_pred h₂, by omega⟩
  · -- `n = N + 2` with `N = n - 2`
    obtain ⟨m₁, m₂, h₁, h₂, hN⟩ := h3a (n - 2) (Nat.dvd_of_mod_eq_zero (by omega)) (by omega)
    exact ⟨m₁ + 1, m₂ + 1, isTPrime_succ h₁, isTPrime_succ h₂, by omega⟩
  · -- `n = N - 2` with `N = n + 2`
    obtain ⟨m₁, m₂, h₁, h₂, hN⟩ := h3a (n + 2) (Nat.dvd_of_mod_eq_zero (by omega)) (by omega)
    have h3 := three_le_of_isMiddleNumber h₁
    have h3' := three_le_of_isMiddleNumber h₂
    exact ⟨m₁ - 1, m₂ - 1, isTPrime_pred h₁, isTPrime_pred h₂, by omega⟩

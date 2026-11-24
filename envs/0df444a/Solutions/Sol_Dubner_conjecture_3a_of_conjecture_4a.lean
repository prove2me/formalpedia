-- Prove2me | solution 1 for Dubner.conjecture_3a_of_conjecture_4a
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-24T12:44:40.501905+00:00
-- url     : https://prove2.me/submissions/6d7cc046-cff3-4c9b-9896-5f66b0533a14

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

open Dubner

namespace DubnerConverse

/-- A multiple of `3` larger than `3` is not prime. -/
theorem not_prime_of_three_dvd {n : ℕ} (h3 : 3 ∣ n) (hn : 3 < n) : ¬ n.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega

/-- A prime `p ≥ 5` is congruent to `1` or `5` modulo `6`. -/
theorem mod_six_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 2 h with h | h <;> omega
  have h3 : ¬ 3 ∣ p := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 h with h | h <;> omega
  omega

/-- A t-prime `t ≡ 5 (mod 6)` has its twin at `t + 2`, so `t + 1` is a middle number. -/
theorem isMiddleNumber_succ {t : ℕ} (ht : IsTPrime t) (h5 : t % 6 = 5) :
    IsMiddleNumber (t + 1) := by
  obtain ⟨htp, h | h⟩ := ht
  · -- `t - 2` is a prime divisible by `3`, hence `t = 5`, whose twin `7` is also prime
    have h3 : 3 ∣ t - 2 := by omega
    have ht5 : t = 5 := by
      rcases h.eq_one_or_self_of_dvd 3 h3 with h1 | h1 <;> omega
    subst ht5
    exact ⟨by norm_num, by norm_num⟩
  · exact ⟨by simpa using htp, by simpa using h⟩

/-- A t-prime `t ≡ 1 (mod 6)` has its twin at `t - 2`, so `t - 1` is a middle number. -/
theorem isMiddleNumber_pred {t : ℕ} (ht : IsTPrime t) (h1 : t % 6 = 1) (h5 : 5 ≤ t) :
    IsMiddleNumber (t - 1) := by
  obtain ⟨htp, h | h⟩ := ht
  · refine ⟨?_, ?_⟩
    · have e : t - 1 - 1 = t - 2 := by omega
      rw [e]
      exact h
    · have e : t - 1 + 1 = t := by omega
      rw [e]
      exact htp
  · -- `t + 2` would be a prime divisible by `3` and larger than `3`
    exfalso
    exact not_prime_of_three_dvd (by omega) (by omega) h

end DubnerConverse

open DubnerConverse in
/-- Dubner's Conjecture 4a implies his Conjecture 3a.

A multiple `N > 4206` of `6` is even and larger than `4208`, so `N = p + q` with t-primes. Neither
is `2` or `3`, so both are `≡ ±1 (mod 6)`, one of each class. The one `≡ 5` has its twin above and
the one `≡ 1` has its twin below, which gives two middle numbers with the same sum. -/
theorem solution
    (h4a : ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q) :
    ∀ N : ℕ, 6 ∣ N → 4206 < N →
      ∃ m₁ m₂ : ℕ, IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂ := by
  intro N h6 hN
  have hNeven : Even N := by
    obtain ⟨k, rfl⟩ := h6
    exact ⟨3 * k, by ring⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := h4a N (by omega) hNeven
  -- in a decomposition `N = a + b` into t-primes, `a ≥ 5`
  have key : ∀ a b : ℕ, IsTPrime a → IsTPrime b → N = a + b → 5 ≤ a := by
    intro a b ha hb hab
    have ha2 : a ≠ 2 := by
      rintro rfl
      exact absurd ha (by decide)
    have ha3 : a ≠ 3 := by
      rintro rfl
      exact not_prime_of_three_dvd (n := b) (by omega) (by omega) hb.1
    have ha4 : a ≠ 4 := by
      rintro rfl
      exact absurd ha.1 (by norm_num)
    have := ha.1.two_le
    omega
  have hp5 := key p q hp hq hpq
  have hq5 := key q p hq hp (by omega)
  rcases mod_six_of_prime hp.1 hp5 with hp1 | hp1 <;>
    rcases mod_six_of_prime hq.1 hq5 with hq1 | hq1
  · omega
  · exact ⟨p - 1, q + 1, isMiddleNumber_pred hp hp1 hp5, isMiddleNumber_succ hq hq1, by omega⟩
  · exact ⟨p + 1, q - 1, isMiddleNumber_succ hp hp1, isMiddleNumber_pred hq hq1 hq5, by omega⟩
  · omega

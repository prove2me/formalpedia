-- Prove2me | solution 1 for Dubner.twin_primes_infinite_of_conjecture_4a
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-24T11:42:15.405011+00:00
-- url     : https://prove2.me/submissions/dd664531-d2eb-4c70-9ff8-d5d563f02f18

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

open Dubner

/-- Dubner's Conjecture 4a implies the twin prime conjecture.

If the set of primes `p` with `p + 2` prime were finite, it would be bounded by some `B`, so every
t-prime would be at most `B + 2`, and the even number `2 * (B + 2105) > 4208` could not be a sum of
two t-primes. -/
theorem solution
    (h4a : ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  -- every t-prime is at most `B + 2`
  have key : ∀ t : ℕ, IsTPrime t → t ≤ B + 2 := by
    intro t ht
    obtain ⟨htp, h | h⟩ := ht
    · -- the twin is `t - 2`: then `t - 2` is the smaller member of a twin pair
      have h2 : 2 ≤ t := htp.two_le
      have hmem : t - 2 ∈ {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} := by
        refine ⟨h, ?_⟩
        have ht2 : t - 2 + 2 = t := by omega
        rw [ht2]
        exact htp
      have hle : t - 2 ≤ B := hB hmem
      omega
    · -- the twin is `t + 2`: then `t` itself is the smaller member of a twin pair
      have hmem : t ∈ {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} := ⟨htp, h⟩
      have hle : t ≤ B := hB hmem
      omega
  obtain ⟨p, q, hp, hq, hpq⟩ := h4a (2 * (B + 2105)) (by omega) (even_two_mul _)
  have hp' := key p hp
  have hq' := key q hq
  omega

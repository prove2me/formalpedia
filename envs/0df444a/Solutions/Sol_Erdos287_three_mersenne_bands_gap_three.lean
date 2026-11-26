-- Prove2me | solution 1 for Erdos287.three_mersenne_bands_gap_three
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T17:04:38.773804+00:00
-- url     : https://prove2.me/submissions/71973f35-ea35-4489-affa-64cb367b847b

import Mathlib
import Theorems.Thm_Erdos287_mersenne_prime_gap_three_band

open Finset

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

/-- Three kernel-checked Mersenne primes give separate bands of maxima. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (e : ℕ) (he : e = 3217 ∨ e = 4253 ∨ e = 4423)
    (hlo : 2 ^ e - 1 ≤ f (k - 1))
    (hhi : 500 * f (k - 1) ≤ 1359 * (2 ^ e - 2)) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  have he' : 5 ≤ e := by omega
  have hp : (mersenne e).Prime := by
    rcases he with rfl | rfl | rfl
    · exact lucas_lehmer_sufficiency 3217 (by decide) (by norm_num)
    · exact lucas_lehmer_sufficiency 4253 (by decide) (by norm_num)
    · exact lucas_lehmer_sufficiency 4423 (by decide) (by norm_num)
  exact Erdos287.mersenne_prime_gap_three_band k hk f hf hmono hsum e he' hp hlo hhi


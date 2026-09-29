-- Prove2me | solution 1 for Freiman.shifted_words_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:53.081826+00:00
-- url     : https://prove2.me/submissions/9da3b5ff-b26b-4895-a848-9c5765169077

import Theorems.Thm_Freiman_bounded_words_subsequence
import Theorems.Thm_Freiman_shift_eventually_digit_bound

open Freiman

theorem solution (a : ℤ → ℕ+) (M N : ℕ)
    (hbound : ∀ n : ℕ, N ≤ n → (a (n : ℤ) : ℕ) ≤ M)
    (u : ℕ → ℕ) (hu : StrictMono u) :
    ∃ v : ℕ → ℕ, StrictMono v ∧
      ∃ b : ℤ → ℕ+,
        (∀ i : ℤ, (b i : ℕ) ≤ M) ∧
        (∀ i : ℤ, ∀ᶠ n in Filter.atTop,
          a ((u (v n) : ℤ) + i) = b i) := by
  exact bounded_words_subsequence (fun n i => a ((u n : ℤ) + i)) M
    (shift_eventually_digit_bound a M N hbound u hu)


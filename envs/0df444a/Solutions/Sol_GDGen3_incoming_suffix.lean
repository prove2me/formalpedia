-- Prove2me | solution 1 for GDGen3.incoming_suffix
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:04:20.354986+00:00
-- url     : https://prove2.me/submissions/9df72018-5063-4211-82d6-812068dfbceb

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ell_of_gt
import Theorems.Thm_GDGen3_D_telescope

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ N) :
    (∑ i ∈ Icc (b + 1) N, ell r ξ N i a) =
      (Am ξ a + r * Abar ξ a) * D r ξ N (b + 1) := by
  by_cases hbN : b = N
  · subst b
    simp [Icc_eq_empty_of_lt (by omega : N < N + 1), D]
  · have ht : ∀ i ∈ Icc (b + 1) N, ell r ξ N i a =
        (Am ξ a + r * Abar ξ a) * (D r ξ N i - D r ξ N (i + 1)) := by
      intro i hi
      exact ell_of_gt r ξ N (by simp only [mem_Icc] at hi; omega)
    rw [sum_congr rfl ht, ← mul_sum, D_telescope r ξ N b (by omega)]

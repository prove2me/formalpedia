-- Prove2me | solution 1 for BookProof.ChapterE2.bornProb_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:30:29.018324+00:00
-- url     : https://prove2.me/submissions/2688f15b-ce52-4c34-aa13-89810a234b9a

-- Generated from ChapterE2.lean — solution of BookProof.ChapterE2.bornProb_sum_eq_one
import Mathlib
import Definitions.Def_ChapterE2
import Theorems.Thm_BookProof_ChapterE2_sum_stick_add_remainder
open BookProof.ChapterE2



open scoped BigOperators
open Finset

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i : Fin n, bornProb θ n i = 1 := by

  rcases n with ( _ | _ | n ) <;> simp_all only [nonpos_iff_eq_zero, one_ne_zero, zero_add, le_refl,
      Nat.reduceAdd, univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton,
          le_add_iff_nonneg_left, zero_le, Fin.sum_univ_castSucc];
  · unfold bornProb; aesop;
  · convert sum_stick_add_remainder θ ( n + 1 ) using 1;
    simp [ Finset.sum_range, Fin.sum_univ_castSucc, bornProb ]

-- Prove2me | solution 1 for BookProof.ChapterNoBestPrior.not_uniformly_better
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:43:17.112732+00:00
-- url     : https://prove2.me/submissions/7261e62a-04be-40a2-91df-1005e787c4ef

-- Generated from ChapterNoBestPrior.lean — solution of BookProof.ChapterNoBestPrior.not_uniformly_better
import Mathlib
import Definitions.Def_ChapterNoBestPrior
import Theorems.Thm_BookProof_ChapterNoBestPrior_eq_of_expectedUtility_ge_all
open BookProof.ChapterNoBestPrior



open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp]

variable {Hyp : Type*} [Fintype Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (p q : Hyp → ℝ) (hpq : p ≠ q) :
    ¬ ∀ u : Hyp → ℝ, expectedUtility q u ≤ expectedUtility p u := by

  exact fun h => hpq <| eq_of_expectedUtility_ge_all p q h ▸ rfl

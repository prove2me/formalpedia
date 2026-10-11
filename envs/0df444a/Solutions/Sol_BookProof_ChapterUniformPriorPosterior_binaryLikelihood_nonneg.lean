-- Prove2me | solution 1 for BookProof.ChapterUniformPriorPosterior.binaryLikelihood_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:14:09.262212+00:00
-- url     : https://prove2.me/submissions/c6eed3da-d01a-40a9-b523-9b9e7e9a8a58

-- Generated from ChapterUniformPriorPosterior.lean — solution of BookProof.ChapterUniformPriorPosterior.binaryLikelihood_nonneg
import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
import Theorems.Thm_BookProof_ChapterUniformPriorPosterior_probability_weight_le_one
open BookProof.ChapterUniformPriorPosterior



open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (q : Hyp → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hq_sum : ∑ x, q x = 1) (x : Hyp) (observed : Bool) :
    0 ≤ binaryLikelihood q x observed := by

  cases observed <;>
    simp [binaryLikelihood, hq_nonneg,
      probability_weight_le_one q hq_nonneg hq_sum]

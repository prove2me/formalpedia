-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.bornWeight_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:37:13.898971+00:00
-- url     : https://prove2.me/submissions/8aaac8e9-8324-4d08-887c-6dd979519bb6

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.bornWeight_sum_one
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornDenom_pos
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j₀ : Fin m) :
    ∑ j, bornWeight q k j = 1 := by

  simp only [bornWeight]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (bornDenom_pos q k j₀))

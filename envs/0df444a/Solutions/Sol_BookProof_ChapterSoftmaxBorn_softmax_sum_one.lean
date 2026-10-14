-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.softmax_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:19:22.723297+00:00
-- url     : https://prove2.me/submissions/4263d3f7-3432-4002-b132-4768428bf2fe

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.softmax_sum_one
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_softmaxDenom_pos
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j₀ : Fin m) :
    ∑ j, softmax beta q k j = 1 := by

  simp only [softmax]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (softmaxDenom_pos beta q k j₀))

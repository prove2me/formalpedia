-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayes.flatPosterior_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:07:40.75448+00:00
-- url     : https://prove2.me/submissions/0ff1d507-9203-4daa-ae66-23949729189c

-- Generated from ChapterHierarchicalBayes.lean — solution of BookProof.ChapterHierarchicalBayes.flatPosterior_sum_one
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
open BookProof.ChapterHierarchicalBayes



open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

variable {A B : Type*} [Fintype A] [Fintype B]

set_option maxHeartbeats 1000000 in
theorem solution (outer : A → ℝ) (inner : A → B → ℝ)
    (likelihood : A → B → ℝ)
    (hEvidence : 0 < hierEvidence outer inner likelihood) :
    ∑ a, ∑ b, flatPosterior outer inner likelihood a b = 1 := by

  unfold flatPosterior hierEvidence
  simp only [jointPrior]
  rw [show ∑ a, ∑ b, outer a * inner a b * likelihood a b /
        (∑ a, ∑ b, outer a * inner a b * likelihood a b) =
      (∑ a, ∑ b, outer a * inner a b * likelihood a b) /
        (∑ a, ∑ b, outer a * inner a b * likelihood a b) by
    rw [Finset.sum_div]
    congr 1 with a
    rw [Finset.sum_div]]
  exact div_self (ne_of_gt hEvidence)

-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayes.jointPrior_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:06:44.522306+00:00
-- url     : https://prove2.me/submissions/c210bf3c-83bf-40e4-8394-7534e7ed121c

-- Generated from ChapterHierarchicalBayes.lean — solution of BookProof.ChapterHierarchicalBayes.jointPrior_nonneg
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
open BookProof.ChapterHierarchicalBayes



open scoped BigOperators


variable {A B : Type*} [Fintype A] [Fintype B]

variable {A B : Type*} [Fintype A] [Fintype B]

set_option maxHeartbeats 1000000 in
theorem solution (outer : A → ℝ) (inner : A → B → ℝ)
    (hOuter : ∀ a, 0 ≤ outer a) (hInner : ∀ a b, 0 ≤ inner a b) :
    ∀ a b, 0 ≤ jointPrior outer inner a b := by

  intro a b
  rw [jointPrior]
  exact mul_nonneg (hOuter a) (hInner a b)

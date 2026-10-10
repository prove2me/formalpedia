-- Prove2me | solution 1 for BookProof.ChapterFiniteBayesHierarchy.collapseKernels_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:20:44.928998+00:00
-- url     : https://prove2.me/submissions/14a03294-f007-4870-83e5-c98c0456292f

-- Generated from ChapterFiniteBayesHierarchy.lean — solution of BookProof.ChapterFiniteBayesHierarchy.collapseKernels_nonnegative
import Mathlib
import Definitions.Def_ChapterFiniteBayesHierarchy
import Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_compKernel_nonnegative
import Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_idKernel_nonnegative
open BookProof.ChapterFiniteBayesHierarchy



open scoped BigOperators


open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]

variable {S : Type*} [Fintype S] [DecidableEq S]

set_option maxHeartbeats 1000000 in
theorem solution (ks : List (S → S → ℝ))
    (hks : ∀ k ∈ ks, IsNonnegativeKernel k) :
    IsNonnegativeKernel (collapseKernels ks) := by

  induction ks with
  | nil => exact idKernel_nonnegative
  | cons k ks ih =>
    simp only [collapseKernels]
    exact compKernel_nonnegative k (collapseKernels ks) (hks k (by simp))
      (ih fun k hk => hks k (by simp only [List.mem_cons]; exact Or.inr hk))

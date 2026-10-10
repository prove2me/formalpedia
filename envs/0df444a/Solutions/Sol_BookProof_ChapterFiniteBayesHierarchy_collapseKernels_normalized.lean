-- Prove2me | solution 1 for BookProof.ChapterFiniteBayesHierarchy.collapseKernels_normalized
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:19:51.753869+00:00
-- url     : https://prove2.me/submissions/2ddd2623-470d-473e-b65d-191cbf79d3ca

-- Generated from ChapterFiniteBayesHierarchy.lean — solution of BookProof.ChapterFiniteBayesHierarchy.collapseKernels_normalized
import Mathlib
import Definitions.Def_ChapterFiniteBayesHierarchy
import Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_compKernel_normalized
import Theorems.Thm_BookProof_ChapterHierarchicalBayesComposition_idKernel_normalized
open BookProof.ChapterFiniteBayesHierarchy



open scoped BigOperators


open BookProof.ChapterHierarchicalBayesComposition

variable {S : Type*} [Fintype S] [DecidableEq S]

variable {S : Type*} [Fintype S] [DecidableEq S]

set_option maxHeartbeats 1000000 in
theorem solution (ks : List (S → S → ℝ))
    (hks : ∀ k ∈ ks, IsNormalizedKernel k) :
    IsNormalizedKernel (collapseKernels ks) := by

  induction ks with
  | nil => exact idKernel_normalized
  | cons k ks ih => 
    simp only [collapseKernels]
    exact compKernel_normalized k (collapseKernels ks) (hks k (by simp)) (ih fun k hk => hks k
                                                                  (by simp only [List.mem_cons];
                                                                      exact Or.inr hk))

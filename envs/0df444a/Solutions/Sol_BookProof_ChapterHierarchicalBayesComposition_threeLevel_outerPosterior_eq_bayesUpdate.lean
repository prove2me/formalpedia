-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayesComposition.threeLevel_outerPosterior_eq_bayesUpdate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:09:47.351979+00:00
-- url     : https://prove2.me/submissions/ddb72d22-5b05-4f61-b5b3-318d61047281

-- Generated from ChapterHierarchicalBayesComposition.lean — solution of BookProof.ChapterHierarchicalBayesComposition.threeLevel_outerPosterior_eq_bayesUpdate
import Mathlib
import Definitions.Def_ChapterHierarchicalBayesComposition
import Theorems.Thm_BookProof_ChapterHierarchicalBayes_outerPosterior_eq_bayesUpdate
import Definitions.Def_ChapterHierarchicalBayes
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterHierarchicalBayesComposition



open scoped BigOperators
open BookProof.ChapterHierarchicalBayes
open BookProof.ChapterSequentialBayes


variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable {A B C D : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

set_option maxHeartbeats 1000000 in
theorem solution (outer : A → ℝ)
    (k₁ : A → B → ℝ) (k₂ : B → C → ℝ) (likelihood : C → ℝ) :
    BookProof.ChapterHierarchicalBayes.outerPosterior outer
        (compKernel k₁ k₂) (fun _ c => likelihood c) =
      BookProof.ChapterSequentialBayes.bayesUpdate outer
        (BookProof.ChapterHierarchicalBayes.marginalLikelihood
          (compKernel k₁ k₂) (fun _ c => likelihood c)) := by

  exact BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate
    outer (compKernel k₁ k₂) (fun _ c => likelihood c)

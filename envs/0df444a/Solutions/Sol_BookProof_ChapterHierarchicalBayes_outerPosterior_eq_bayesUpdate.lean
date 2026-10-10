-- Prove2me | solution 1 for BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:37:16.308151+00:00
-- url     : https://prove2.me/submissions/dab38e2f-4eda-4fd8-9bd5-14a717b9fea6

-- Generated from ChapterHierarchicalBayes.lean — solution of BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate
import Mathlib
import Definitions.Def_ChapterHierarchicalBayes
import Theorems.Thm_BookProof_ChapterHierarchicalBayes_evidence_eq_marginal
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterHierarchicalBayes



open scoped BigOperators
open BookProof.ChapterSequentialBayes


variable {A B : Type*} [Fintype A] [Fintype B]

variable {A B : Type*} [Fintype A] [Fintype B]

set_option maxHeartbeats 1000000 in
theorem solution (outer : A → ℝ) (inner : A → B → ℝ)
    (likelihood : A → B → ℝ) :
    outerPosterior outer inner likelihood =
      BookProof.ChapterSequentialBayes.bayesUpdate outer
        (marginalLikelihood inner likelihood) := by

  funext a
  unfold outerPosterior BookProof.ChapterSequentialBayes.bayesUpdate
  rw [evidence_eq_marginal]

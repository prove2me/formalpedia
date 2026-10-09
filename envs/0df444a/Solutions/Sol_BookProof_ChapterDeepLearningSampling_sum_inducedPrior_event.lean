-- Prove2me | solution 1 for BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:48:56.719849+00:00
-- url     : https://prove2.me/submissions/b9a73f62-569b-4ddf-9e54-18508d47e65a

-- Generated from ChapterDeepLearningSampling.lean — solution of BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event
import Mathlib
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterDeepLearningSampling



open scoped BigOperators


variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]

variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]

set_option maxHeartbeats 1000000 in
theorem solution
    (seedProb : Seed → ℝ) (train : Seed → Model)
    (A : Finset Model) :
    ∑ m ∈ A, inducedPrior seedProb train m = ∑ s with train s ∈ A, seedProb s := by

  simp only [inducedPrior]
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ A train seedProb

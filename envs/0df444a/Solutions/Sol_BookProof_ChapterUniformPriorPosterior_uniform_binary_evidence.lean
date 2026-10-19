-- Prove2me | solution 1 for BookProof.ChapterUniformPriorPosterior.uniform_binary_evidence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:55.228757+00:00
-- url     : https://prove2.me/submissions/78379864-212f-420e-ae48-96f8729dd143

import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterUniformPriorPosterior.lean — theorem BookProof.ChapterUniformPriorPosterior.uniform_binary_evidence
open BookProof.ChapterBayesInference
open BookProof.ChapterUniformPriorPosterior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]


theorem solution (q : Hyp → ℝ) (hq_sum : ∑ x, q x = 1)
    (c : ℝ) :
    BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c)
      (binaryLikelihood q) true = c := by
  simp [BookProof.ChapterBayesInference.evidence, binaryLikelihood, ← Finset.mul_sum, hq_sum]


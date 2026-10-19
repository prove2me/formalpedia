-- Prove2me | solution 1 for BookProof.ChapterUniformPriorPosterior.uniform_prior_posterior_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:40:02.862625+00:00
-- url     : https://prove2.me/submissions/68a2e9c2-1a4f-4dbd-b2fc-9bd3d2fd74cf

import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterUniformPriorPosterior.lean — theorem BookProof.ChapterUniformPriorPosterior.uniform_prior_posterior_eq
open BookProof.ChapterBayesInference
open BookProof.ChapterUniformPriorPosterior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]


theorem solution (q : Hyp → ℝ) (hq_sum : ∑ x, q x = 1)
    (c : ℝ) (hc : 0 < c) (x : Hyp) :
    BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c)
      (binaryLikelihood q) true x = q x := by
  have he : BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) (binaryLikelihood q) true = c := by
    simp [BookProof.ChapterBayesInference.evidence, binaryLikelihood, ← Finset.mul_sum, hq_sum]
  unfold BookProof.ChapterBayesInference.posterior
  rw [he]
  simp [binaryLikelihood]
  field_simp


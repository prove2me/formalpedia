-- Prove2me | solution 1 for BookProof.ChapterUniformPriorPosterior.exists_likelihood_uniform_prior_posterior
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:14:38.228246+00:00
-- url     : https://prove2.me/submissions/7b295f2f-efb4-4391-9d33-b0c5ea11640b

-- Generated from ChapterUniformPriorPosterior.lean — solution of BookProof.ChapterUniformPriorPosterior.exists_likelihood_uniform_prior_posterior
import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
import Theorems.Thm_BookProof_ChapterUniformPriorPosterior_binaryLikelihood_nonneg
import Theorems.Thm_BookProof_ChapterUniformPriorPosterior_binaryLikelihood_sum
import Theorems.Thm_BookProof_ChapterUniformPriorPosterior_uniform_prior_posterior_eq
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterUniformPriorPosterior



open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (q : Hyp → ℝ)
    (hq_nonneg : ∀ x, 0 ≤ q x) (hq_sum : ∑ x, q x = 1)
    (c : ℝ) (hc : 0 < c) :
    ∃ L : Hyp → Bool → ℝ,
      (∀ x observed, 0 ≤ L x observed) ∧
      (∀ x, ∑ observed, L x observed = 1) ∧
      (∀ x, BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c)
        L true x = q x) := by

  refine ⟨binaryLikelihood q, ?_, binaryLikelihood_sum q, ?_⟩
  · exact binaryLikelihood_nonneg q hq_nonneg hq_sum
  · exact uniform_prior_posterior_eq q hq_sum c hc

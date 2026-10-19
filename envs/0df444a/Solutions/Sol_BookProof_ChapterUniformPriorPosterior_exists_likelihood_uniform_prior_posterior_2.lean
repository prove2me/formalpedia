-- Prove2me | solution 2 for BookProof.ChapterUniformPriorPosterior.exists_likelihood_uniform_prior_posterior
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:40:15.279658+00:00
-- url     : https://prove2.me/submissions/09e73a9a-1942-48a1-b94f-0b891b17f233

import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterUniformPriorPosterior.lean — theorem BookProof.ChapterUniformPriorPosterior.exists_likelihood_uniform_prior_posterior
open BookProof.ChapterBayesInference
open BookProof.ChapterUniformPriorPosterior


open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]


theorem solution (q : Hyp → ℝ)
    (hq_nonneg : ∀ x, 0 ≤ q x) (hq_sum : ∑ x, q x = 1)
    (c : ℝ) (hc : 0 < c) :
    ∃ L : Hyp → Bool → ℝ,
      (∀ x observed, 0 ≤ L x observed) ∧
      (∀ x, ∑ observed, L x observed = 1) ∧
      (∀ x, BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c)
        L true x = q x) := by
  have hle : ∀ x, q x ≤ 1 := fun x => by
    rw [← hq_sum]
    exact Finset.single_le_sum (fun y _ => hq_nonneg y) (Finset.mem_univ x)
  have he : BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) (binaryLikelihood q) true = c := by
    simp [BookProof.ChapterBayesInference.evidence, binaryLikelihood, ← Finset.mul_sum, hq_sum]
  refine ⟨binaryLikelihood q, ?_, ?_, ?_⟩
  · intro x o
    cases o <;> simp [binaryLikelihood, hq_nonneg x, hle x]
  · intro x
    simp [binaryLikelihood]
  · intro x
    unfold BookProof.ChapterBayesInference.posterior
    rw [he]
    simp [binaryLikelihood]
    field_simp


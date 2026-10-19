-- Prove2me | solution 1 for BookProof.ChapterUniformPrior.uniform_prior_posterior_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:53:06.998979+00:00
-- url     : https://prove2.me/submissions/3a4ebae4-d178-45ca-b0ff-2354645ae0f8

import Mathlib
import Definitions.Def_ChapterUniformPrior
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterUniformPrior.lean — theorem BookProof.ChapterUniformPrior.uniform_prior_posterior_le_iff
open BookProof.ChapterBayesInference
open BookProof.ChapterUniformPrior


open scoped BigOperators


variable {Hyp Data : Type*}


theorem solution [Fintype Hyp]
    (likelihood : Hyp → Data → ℝ) (d : Data) (c : ℝ)
    (hc : 0 < c)
    (hevidence : 0 < BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) likelihood d)
    (a b : Hyp) :
    BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d a ≤
        BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d b ↔
      likelihood a d ≤ likelihood b d := by
  unfold BookProof.ChapterBayesInference.posterior
  rw [div_le_div_iff_of_pos_right hevidence]
  exact mul_le_mul_iff_of_pos_left hc


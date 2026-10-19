-- Prove2me | solution 2 for BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:53:22.204999+00:00
-- url     : https://prove2.me/submissions/f9ffcaa4-5b05-4078-b618-d0c4473dca58

import Mathlib
import Definitions.Def_ChapterUniformPrior
import Definitions.Def_ChapterBayesInference
-- Generated from ChapterUniformPrior.lean — theorem BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE
open BookProof.ChapterBayesInference
open BookProof.ChapterUniformPrior


open scoped BigOperators


variable {Hyp Data : Type*}


theorem solution [Fintype Hyp]
    (likelihood : Hyp → Data → ℝ) (d : Data) (c : ℝ)
    (hc : 0 < c)
    (hevidence : 0 < BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) likelihood d)
    (best : Hyp) :
    (∀ m, BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d m ≤
        BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d best) ↔
      ∀ m, likelihood m d ≤ likelihood best d := by
  have key : ∀ a b : Hyp, BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d a ≤
      BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d b ↔
      likelihood a d ≤ likelihood b d := by
    intro a b
    unfold BookProof.ChapterBayesInference.posterior
    rw [div_le_div_iff_of_pos_right hevidence]
    exact mul_le_mul_iff_of_pos_left hc
  exact forall_congr' fun m => key m best


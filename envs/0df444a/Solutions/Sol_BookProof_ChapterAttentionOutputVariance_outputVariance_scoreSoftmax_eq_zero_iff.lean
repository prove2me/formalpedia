-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:42:02.68241+00:00
-- url     : https://prove2.me/submissions/d4b398ec-459f-44b5-a9e7-e60c50b69fd3

import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Definitions.Def_ChapterSoftmaxSharpness
-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutputVariance


open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem solution (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) :
    outputVariance (scoreSoftmax beta s) v = 0 ↔ ∀ j, v j = headOutput beta s v := by
  have hpos : ∀ j, 0 < scoreSoftmax beta s j := fun j =>
    div_pos (Real.exp_pos _) (Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩)
  unfold outputVariance
  have hμ : observableExpectation (scoreSoftmax beta s) v = headOutput beta s v := rfl
  rw [hμ, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _))]
  constructor
  · intro h j
    have := h j (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (hpos j).ne'
    · rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h1; exact h1
  · intro h j _
    rw [← h j, sub_self, norm_zero]; ring

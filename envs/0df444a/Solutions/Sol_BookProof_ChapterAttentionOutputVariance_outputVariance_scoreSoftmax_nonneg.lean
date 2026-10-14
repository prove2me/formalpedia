-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:38:59.57189+00:00
-- url     : https://prove2.me/submissions/c9f89a43-099c-4b6c-bc86-0f1fbca40745

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_nonneg
import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutputVariance


open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open BookProof.ChapterAttentionOutputVariance

theorem solution(beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) :
    0 ≤ outputVariance (scoreSoftmax beta s) v := by
  unfold outputVariance
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg _ (sq_nonneg _)
  unfold scoreSoftmax
  positivity

-- Prove2me | solution 1 for BookProof.ChapterSoftmaxDivergence.fisherInformation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:38:38.608994+00:00
-- url     : https://prove2.me/submissions/28dd5e19-3f84-42eb-954e-0f89b6355745

-- Generated from ChapterSoftmaxDivergence.lean — theorem BookProof.ChapterSoftmaxDivergence.fisherInformation_nonneg
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
open BookProof.ChapterSoftmaxDivergence


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}
open BookProof.ChapterSoftmaxDivergence

theorem solution(beta : ℝ) (s : Fin m → ℝ) :
    0 ≤ fisherInformation beta s := by
  unfold fisherInformation scoreSoftmax
  apply Finset.sum_nonneg
  intro l _
  apply mul_nonneg _ (sq_nonneg _)
  apply div_nonneg (Real.exp_pos _).le
  exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

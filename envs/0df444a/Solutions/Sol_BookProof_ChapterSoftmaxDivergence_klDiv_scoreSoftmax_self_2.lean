-- Prove2me | solution 2 for BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax_self
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:15:28.929028+00:00
-- url     : https://prove2.me/submissions/d77c50b9-4686-479c-978b-7c06e9bb3375

-- Generated from ChapterSoftmaxDivergence.lean — theorem BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax_self
import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxDivergence


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}
open BookProof.ChapterSoftmaxDivergence

theorem solution(beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    klDiv (scoreSoftmax beta s) (scoreSoftmax beta s) = 0 := by
  unfold klDiv
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : scoreSoftmax beta s j = 0 <;> simp [h]

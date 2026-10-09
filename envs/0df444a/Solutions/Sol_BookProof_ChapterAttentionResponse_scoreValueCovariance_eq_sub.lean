-- Prove2me | solution 1 for BookProof.ChapterAttentionResponse.scoreValueCovariance_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:37:48.204294+00:00
-- url     : https://prove2.me/submissions/8c5d44e8-1d4d-4328-b8c3-87c7db33c930

-- Generated from ChapterAttentionResponse.lean — solution of BookProof.ChapterAttentionResponse.scoreValueCovariance_eq_sub
import Mathlib
import Definitions.Def_ChapterAttentionResponse
import Theorems.Thm_BookProof_ChapterAttentionOutput_headOutput_eq_sum
import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterSoftmaxFluctuation
open BookProof.ChapterAttentionResponse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) :
    scoreValueCovariance beta s v
      = (∑ j, (scoreSoftmax beta s j * s j) • v j) - meanScore beta s • headOutput beta s v := by

  rw [scoreValueCovariance, headOutput_eq_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← sub_smul]
  ring_nf

-- Prove2me | solution 1 for BookProof.ChapterAttentionResponse.scoreValueCovariance_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:17.478647+00:00
-- url     : https://prove2.me/submissions/5afeaac4-2b15-4fac-bf6c-b3c684930f68

-- Generated from ChapterAttentionResponse.lean — solution of BookProof.ChapterAttentionResponse.scoreValueCovariance_const
import Mathlib
import Definitions.Def_ChapterAttentionResponse
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation
open BookProof.ChapterAttentionResponse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (w : E) (i : Fin m) :
    scoreValueCovariance beta s (fun _ => w) = (0 : E) := by

  have hsum : ∑ j, scoreSoftmax beta s j * (s j - meanScore beta s) = 0 := by
    have h1 : ∑ j, scoreSoftmax beta s j = 1 := scoreSoftmax_sum_one beta s i
    have : ∑ j, scoreSoftmax beta s j * (s j - meanScore beta s)
        = (∑ j, scoreSoftmax beta s j * s j)
          - (∑ j, scoreSoftmax beta s j) * meanScore beta s := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, h1, one_mul, ← meanScore, sub_self]
  rw [scoreValueCovariance, ← Finset.sum_smul, hsum, zero_smul]

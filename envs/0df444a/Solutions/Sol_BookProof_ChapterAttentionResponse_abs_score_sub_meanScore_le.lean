-- Prove2me | solution 1 for BookProof.ChapterAttentionResponse.abs_score_sub_meanScore_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:19.602822+00:00
-- url     : https://prove2.me/submissions/a9d01340-65bf-46fc-89b9-f1aa16d73f34

-- Generated from ChapterAttentionResponse.lean — solution of BookProof.ChapterAttentionResponse.abs_score_sub_meanScore_le
import Mathlib
import Definitions.Def_ChapterAttentionResponse
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
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
theorem solution {s : Fin m → ℝ} {a b : ℝ} (ha : ∀ l, a ≤ s l)
    (hb : ∀ l, s l ≤ b) (beta : ℝ) (j : Fin m) : |s j - meanScore beta s| ≤ b - a := by

  have h1 : meanScore beta s ≤ b := by
    have hsum : ∑ l, scoreSoftmax beta s l = 1 := scoreSoftmax_sum_one beta s j
    calc meanScore beta s ≤ ∑ l, scoreSoftmax beta s l * b :=
          Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (hb l) (scoreSoftmax_nonneg beta s l)
      _ = b := by rw [← Finset.sum_mul, hsum, one_mul]
  have h2 : a ≤ meanScore beta s := by
    have hsum : ∑ l, scoreSoftmax beta s l = 1 := scoreSoftmax_sum_one beta s j
    calc a = ∑ l, scoreSoftmax beta s l * a := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ meanScore beta s :=
          Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (ha l) (scoreSoftmax_nonneg beta s l)
  rw [abs_le]
  constructor
  · have := ha j; linarith
  · have := hb j; linarith

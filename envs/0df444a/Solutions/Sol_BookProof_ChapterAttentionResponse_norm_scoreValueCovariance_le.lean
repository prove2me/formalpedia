-- Prove2me | solution 1 for BookProof.ChapterAttentionResponse.norm_scoreValueCovariance_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:18.592837+00:00
-- url     : https://prove2.me/submissions/ebe04fdf-4116-4447-a3d2-3425b920c10f

-- Generated from ChapterAttentionResponse.lean — solution of BookProof.ChapterAttentionResponse.norm_scoreValueCovariance_le
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
theorem solution (beta : ℝ) {s : Fin m → ℝ} {v : Fin m → E} {C D : ℝ}
    (hv : ∀ j, ‖v j‖ ≤ C) (hs : ∀ j, |s j - meanScore beta s| ≤ D) (i : Fin m) :
    ‖scoreValueCovariance beta s v‖ ≤ C * D := by

  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv i)
  have hterm : ∀ j : Fin m,
      ‖(scoreSoftmax beta s j * (s j - meanScore beta s)) • v j‖
        ≤ scoreSoftmax beta s j * (C * D) := by
    intro j
    rw [norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (scoreSoftmax_nonneg beta s j)]
    have h1 : |s j - meanScore beta s| * ‖v j‖ ≤ D * C := by
      have hD : 0 ≤ D := le_trans (abs_nonneg _) (hs j)
      exact mul_le_mul (hs j) (hv j) (norm_nonneg _) hD
    calc scoreSoftmax beta s j * |s j - meanScore beta s| * ‖v j‖
        = scoreSoftmax beta s j * (|s j - meanScore beta s| * ‖v j‖) := by ring
      _ ≤ scoreSoftmax beta s j * (D * C) :=
          mul_le_mul_of_nonneg_left h1 (scoreSoftmax_nonneg beta s j)
      _ = scoreSoftmax beta s j * (C * D) := by ring
  calc ‖scoreValueCovariance beta s v‖
      ≤ ∑ j, ‖(scoreSoftmax beta s j * (s j - meanScore beta s)) • v j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, scoreSoftmax beta s j * (C * D) := Finset.sum_le_sum fun j _ => hterm j
    _ = C * D := by rw [← Finset.sum_mul, scoreSoftmax_sum_one beta s i, one_mul]

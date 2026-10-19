-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:49.72098+00:00
-- url     : https://prove2.me/submissions/180cf12b-a9cf-47e4-89da-084197cce4dc

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_deriv_scoreSoftmax_beta
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_differentiable_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_meanScore_le_max
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxTemperatureMonotone



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) :
    Monotone fun b : ℝ => scoreSoftmax b s j := by
  refine monotone_of_deriv_nonneg (differentiable_scoreSoftmax s j) fun b => ?_
  rw [deriv_scoreSoftmax_beta b s j]
  have hmean : meanScore b s ≤ s j := meanScore_le_max b s j hmax
  exact mul_nonneg (scoreSoftmax_nonneg b s j) (by linarith)

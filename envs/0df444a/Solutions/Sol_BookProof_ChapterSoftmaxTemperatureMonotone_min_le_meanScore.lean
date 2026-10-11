-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.min_le_meanScore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:48.732318+00:00
-- url     : https://prove2.me/submissions/f773fd44-d962-4b2a-8736-41761c31520a

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.min_le_meanScore
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
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

theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m)
    (hmin : ∀ l, s i ≤ s l) : s i ≤ meanScore beta s := by
  have hsum : ∑ l, scoreSoftmax beta s l = 1 := scoreSoftmax_sum_one beta s i
  calc s i = ∑ l, scoreSoftmax beta s l * s i := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ meanScore beta s :=
        Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (hmin l) (scoreSoftmax_nonneg beta s l)

/-! ## Sharpening is monotone -/

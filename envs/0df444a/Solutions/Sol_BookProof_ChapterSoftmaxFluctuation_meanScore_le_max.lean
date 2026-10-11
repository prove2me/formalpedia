-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.meanScore_le_max
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:54.101323+00:00
-- url     : https://prove2.me/submissions/8e468729-3de3-4db3-8410-d457835db91b

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.meanScore_le_max
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m)
    (hmax : ∀ l, s l ≤ s i) : meanScore beta s ≤ s i := by

  have hsum : ∑ l, scoreSoftmax beta s l = 1 := scoreSoftmax_sum_one beta s i
  calc meanScore beta s ≤ ∑ l, scoreSoftmax beta s l * s i :=
        Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (hmax l) (scoreSoftmax_nonneg beta s l)
    _ = s i := by rw [← Finset.sum_mul, hsum, one_mul]

-- Prove2me | solution 2 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:35:55.857121+00:00
-- url     : https://prove2.me/submissions/f197273e-f455-434e-b4de-0df53ed3b345

import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Definitions.Def_ChapterSoftmaxSharpness
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_deriv_scoreSoftmax_beta
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_min_le_meanScore
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_meanScore_le_max
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_scoreSoftmax_zero
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxTemperatureMonotone


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}
theorem h44_mono (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) :
    Monotone fun b : ℝ => BookProof.ChapterSoftmaxSharpness.scoreSoftmax b s j := by
  apply monotone_of_deriv_nonneg
  · exact fun b => (BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax b s j).differentiableAt
  · intro b
    rw [BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta]
    exact mul_nonneg (BookProof.ChapterSoftmaxOrder.scoreSoftmax_nonneg b s j)
      (sub_nonneg.mpr (BookProof.ChapterSoftmaxFluctuation.meanScore_le_max b s j hmax))

theorem solution {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, s l ≤ s j) : 1 / (m : ℝ) ≤ scoreSoftmax beta s j := by
  have h : scoreSoftmax 0 s j ≤ scoreSoftmax beta s j := h44_mono s j hmax hb
  rw [BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero] at h
  exact h


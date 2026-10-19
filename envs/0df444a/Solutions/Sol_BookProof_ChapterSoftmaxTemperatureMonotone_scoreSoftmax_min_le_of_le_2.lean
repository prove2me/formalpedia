-- Prove2me | solution 2 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:35:48.344397+00:00
-- url     : https://prove2.me/submissions/d931d444-b851-4d25-8193-7a7f4e1bbf36

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
-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxTemperatureMonotone


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}
theorem h44_anti (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) :
    Antitone fun b : ℝ => BookProof.ChapterSoftmaxSharpness.scoreSoftmax b s i := by
  apply antitone_of_deriv_nonpos
  · exact fun b => (BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax b s i).differentiableAt
  · intro b
    rw [BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta]
    exact mul_nonpos_of_nonneg_of_nonpos (BookProof.ChapterSoftmaxOrder.scoreSoftmax_nonneg b s i)
      (sub_nonpos.mpr (BookProof.ChapterSoftmaxTemperatureMonotone.min_le_meanScore b s i hmin))

theorem solution {beta gamma : ℝ} (hbg : beta ≤ gamma) (s : Fin m → ℝ)
    (i : Fin m) (hmin : ∀ l, s i ≤ s l) :
    scoreSoftmax gamma s i ≤ scoreSoftmax beta s i := by
  exact h44_anti s i hmin hbg


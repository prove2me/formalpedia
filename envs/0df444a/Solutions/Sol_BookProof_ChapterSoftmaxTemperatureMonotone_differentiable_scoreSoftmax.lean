-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.differentiable_scoreSoftmax
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:34:34.570521+00:00
-- url     : https://prove2.me/submissions/c93edaeb-80be-4306-b2f3-7619f1ed0197

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
-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.differentiable_scoreSoftmax
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxTemperatureMonotone


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}


theorem solution (s : Fin m → ℝ) (j : Fin m) :
    Differentiable ℝ fun b : ℝ => scoreSoftmax b s j := by
  exact fun b => (BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax b s j).differentiableAt


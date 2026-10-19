-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_inv_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:45:14.013821+00:00
-- url     : https://prove2.me/submissions/d9110c8d-2001-4741-813a-5907846fb0a8

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_inv_card
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_min_le_of_le
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_scoreSoftmax_zero
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxTemperatureMonotone



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (i : Fin m)
    (hmin : ∀ l, s i ≤ s l) : scoreSoftmax beta s i ≤ 1 / (m : ℝ) := by

  have h := scoreSoftmax_min_le_of_le hb s i hmin
  rwa [scoreSoftmax_zero] at h

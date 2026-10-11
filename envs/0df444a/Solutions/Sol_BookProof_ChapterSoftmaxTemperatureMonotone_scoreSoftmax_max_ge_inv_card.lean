-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:45:13.015076+00:00
-- url     : https://prove2.me/submissions/7329f3f1-c1cc-48b7-b422-6dcbec931b23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_max_ge_of_le
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
theorem solution {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, s l ≤ s j) : 1 / (m : ℝ) ≤ scoreSoftmax beta s j := by

  have h := scoreSoftmax_max_ge_of_le hb s j hmax
  rwa [scoreSoftmax_zero] at h

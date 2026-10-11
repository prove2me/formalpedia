-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:31.879999+00:00
-- url     : https://prove2.me/submissions/a4bab6b3-0051-4671-9e93-44564909e83c

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_iff
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_denom_pos
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (i j : Fin m) :
    scoreSoftmax beta s i ≤ scoreSoftmax beta s j ↔ s i ≤ s j := by

  rw [scoreSoftmax, scoreSoftmax,
    div_le_div_iff_of_pos_right (scoreSoftmax_denom_pos beta s i), Real.exp_le_exp,
    mul_le_mul_iff_of_pos_left hbeta]

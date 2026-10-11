-- Prove2me | solution 1 for BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_target_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:31.371185+00:00
-- url     : https://prove2.me/submissions/5a682cf5-ee96-44ed-9e82-1f5743e6df2b

-- Generated from ChapterCrossEntropyGradient.lean — solution of BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_target_nonpos
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_le_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterCrossEntropyGradient



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (y : Fin m) : crossEntropyGradient beta s y y ≤ 0 := by

  have h := scoreSoftmax_le_one beta s y
  have : scoreSoftmax beta s y - 1 ≤ 0 := by linarith
  simpa [crossEntropyGradient] using mul_nonpos_of_nonneg_of_nonpos hb this

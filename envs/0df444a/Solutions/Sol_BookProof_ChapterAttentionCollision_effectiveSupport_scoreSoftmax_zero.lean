-- Prove2me | solution 1 for BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:00.908553+00:00
-- url     : https://prove2.me/submissions/58a286c5-9af4-4cf1-9a66-691ec248a218

-- Generated from ChapterAttentionCollision.lean — solution of BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero
import Mathlib
import Definitions.Def_ChapterAttentionCollision
import Theorems.Thm_BookProof_ChapterAttentionCollision_effectiveSupport_uniform
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_scoreSoftmax_zero
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionCollision



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin m → ℝ) (i : Fin m) :
    effectiveSupport (scoreSoftmax 0 s) = (m : ℝ) := by

  have hm : 0 < m := Fin.pos i
  have : scoreSoftmax (0 : ℝ) s = fun _ : Fin m => (1 : ℝ) / m := by
    funext j; exact scoreSoftmax_zero s j
  rw [this, effectiveSupport_uniform hm]

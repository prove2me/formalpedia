-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.maskedSoftmax_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:29:02.149791+00:00
-- url     : https://prove2.me/submissions/f16b6368-1eae-41d1-8fdf-2bcaf21f70a4

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.maskedSoftmax_of_mem
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterAttentionMasking



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m}
    (hj : j ∈ S) :
    maskedSoftmax beta s S j = Real.exp (beta * s j) / ∑ l ∈ S, Real.exp (beta * s l) := by

  rw [maskedSoftmax, if_pos hj]

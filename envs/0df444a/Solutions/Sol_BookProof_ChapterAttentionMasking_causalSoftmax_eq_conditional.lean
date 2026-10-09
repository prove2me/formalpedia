-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.causalSoftmax_eq_conditional
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:08:10.093753+00:00
-- url     : https://prove2.me/submissions/09f83510-2be2-480a-8277-570efb6aa858
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.causalSoftmax_eq_conditional
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_eq_conditional
import Theorems.Thm_BookProof_ChapterAttentionMasking_mem_causalMask
open BookProof.ChapterAttentionMasking



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {i j : Fin m} (hij : j ≤ i) :
    maskedSoftmax beta s (causalMask m i) j
      = scoreSoftmax beta s j / ∑ l ∈ causalMask m i, scoreSoftmax beta s l := maskedSoftmax_eq_conditional beta s (mem_causalMask.2 hij)

-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.causalSoftmax_eq_zero_of_lt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:07:25.153989+00:00
-- url     : https://prove2.me/submissions/c55ca6fd-453e-4ca7-9eb3-164919433356
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.causalSoftmax_eq_zero_of_lt
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_eq_zero_of_not_mem
import Theorems.Thm_BookProof_ChapterAttentionMasking_mem_causalMask
open BookProof.ChapterAttentionMasking



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {i j : Fin m} (hij : i < j) :
    maskedSoftmax beta s (causalMask m i) j = 0 := maskedSoftmax_eq_zero_of_not_mem beta s (by simp [mem_causalMask, not_le.2 hij])

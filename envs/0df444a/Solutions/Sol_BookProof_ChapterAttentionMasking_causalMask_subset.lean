-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.causalMask_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:08:09.048218+00:00
-- url     : https://prove2.me/submissions/4121b857-1977-4c68-9598-d3ecb3de51ab

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.causalMask_subset
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Theorems.Thm_BookProof_ChapterAttentionMasking_mem_causalMask
open BookProof.ChapterAttentionMasking



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {i i' : Fin m} (h : i ≤ i') : causalMask m i ⊆ causalMask m i' := fun _ hl => mem_causalMask.2 (le_trans (mem_causalMask.1 hl) h)

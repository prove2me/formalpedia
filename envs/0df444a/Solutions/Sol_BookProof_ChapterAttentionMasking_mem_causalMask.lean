-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.mem_causalMask
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:31:40.5858+00:00
-- url     : https://prove2.me/submissions/01971932-c299-4a30-a2b9-1373328e4e4c

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.mem_causalMask
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
theorem solution {i l : Fin m} : l ∈ causalMask m i ↔ l ≤ i := by

  simp [causalMask]

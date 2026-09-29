-- Prove2me | solution 1 for BookProof.ChapterSirkMultiShift.multiShiftSeq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:50:36.577258+00:00
-- url     : https://prove2.me/submissions/2a84fd42-5d39-4c69-a063-354ea296eda0

-- Generated from ChapterSirkMultiShift.lean — solution of BookProof.ChapterSirkMultiShift.multiShiftSeq_zero
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift











noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[K] E) (z : ℕ → K) (v : E) :
    multiShiftSeq H z v 0 = v := rfl

-- Prove2me | solution 1 for BookProof.ChapterSirkMultiShift.multiShiftSeq_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:49:06.916044+00:00
-- url     : https://prove2.me/submissions/ce990325-0632-457c-bb61-e78de834b1db

-- Generated from ChapterSirkMultiShift.lean — solution of BookProof.ChapterSirkMultiShift.multiShiftSeq_succ
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift











noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (k : ℕ) :
    multiShiftSeq H z v (k + 1) = H (multiShiftSeq H z v k) - z k • multiShiftSeq H z v k := by

  change (H - z k • 1) (multiShiftSeq H z v k) = _
  simp

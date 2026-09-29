-- Prove2me | solution 1 for BookProof.ChapterSirkMultiShift.multiShiftSeq_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:47:47.760342+00:00
-- url     : https://prove2.me/submissions/78565f9b-5430-42b5-8d28-8e05c7dc6c4b

-- Generated from ChapterSirkMultiShift.lean — solution of BookProof.ChapterSirkMultiShift.multiShiftSeq_const
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift











noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[K] E) (γ : K) (v : E) (k : ℕ) :
    multiShiftSeq H (fun _ => γ) v k = noInversionSeq H γ v k := by

  induction k with
  | zero => rfl
  | succ k ih => rw [multiShiftSeq, ih]; rfl

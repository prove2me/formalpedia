-- Prove2me | solution 1 for BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T08:04:29.177983+00:00
-- url     : https://prove2.me/submissions/864f50be-6c44-4894-8caf-7285a388274b

-- Generated from ChapterSirkMultiShift.lean — solution of BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
import Theorems.Thm_BookProof_ChapterSirkMultiShift_krylov_multiShift_eq_standard
open BookProof.ChapterSirkMultiShift











noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[K] E) (z z' : ℕ → K) (v : E) (m : ℕ) :
    Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z v i}
      = Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z' v i} := by

  rw [krylov_multiShift_eq_standard, krylov_multiShift_eq_standard]

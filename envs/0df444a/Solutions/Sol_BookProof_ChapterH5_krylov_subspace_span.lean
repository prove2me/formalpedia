-- Prove2me | solution 1 for BookProof.ChapterH5.krylov_subspace_span
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:58:12.277319+00:00
-- url     : https://prove2.me/submissions/3ca14d7d-b26a-45a6-8504-f9f4c39f55ff

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.krylov_subspace_span
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[K] E) (v : E) (m : ℕ) :
    krylovSpan H v m = Submodule.span K {x | ∃ i < m, x = (H ^ i) v} := rfl

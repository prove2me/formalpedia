-- Prove2me | solution 1 for BookProof.ChapterH5.generator_bounded_of_rankOneProjector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:36:46.834975+00:00
-- url     : https://prove2.me/submissions/0a97dbdd-30a0-444a-9174-a98de59f25a1

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.generator_bounded_of_rankOneProjector
import Mathlib
import Definitions.Def_ChapterH5
import Theorems.Thm_BookProof_ChapterH5_norm_rankOneProj_le
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (u : E) (hu : ‖u‖ = 1) (D : E →L[ℂ] E) :
    ‖rankOneProj u + D‖ ≤ 1 + ‖D‖ := by

  refine le_trans (norm_add_le _ _) ?_
  have h := norm_rankOneProj_le u
  rw [hu] at h
  simpa using add_le_add_right (by simpa using h) ‖D‖

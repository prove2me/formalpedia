-- Prove2me | solution 1 for BookProof.ChapterH5.norm_rankOneProj_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:36:45.406934+00:00
-- url     : https://prove2.me/submissions/d4126f0e-2113-4caa-b24c-3e356f7a74ec

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.norm_rankOneProj_le
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (u : E) : ‖rankOneProj u‖ ≤ ‖u‖ * ‖u‖ := by

  rw [rankOneProj, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

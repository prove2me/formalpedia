-- Prove2me | solution 1 for BookProof.ChapterH5.inversion_free_seed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:59:12.496289+00:00
-- url     : https://prove2.me/submissions/f73e02f2-b50c-4a84-91be-5d8ca7079070

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.inversion_free_seed
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (S R : E →ₗ[K] E) (v₀ : E) (m : ℕ)
    (hR : R.comp S = LinearMap.id) :
    R ((S ^ (m + 1)) v₀) = (S ^ m) v₀ := by

  have hstep : ((S ^ (m + 1)) v₀) = S ((S ^ m) v₀) := by
    rw [pow_succ']; rfl
  rw [hstep]
  exact congrArg (fun f : E →ₗ[K] E => f ((S ^ m) v₀)) hR

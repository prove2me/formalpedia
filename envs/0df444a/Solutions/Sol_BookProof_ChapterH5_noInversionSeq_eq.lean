-- Prove2me | solution 1 for BookProof.ChapterH5.noInversionSeq_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:59:13.570662+00:00
-- url     : https://prove2.me/submissions/1ef87e1f-7657-4b21-9d51-b754bd6fd5c5

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.noInversionSeq_eq
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[K] E) (γ : K) (v : E) (k : ℕ) :
    noInversionSeq H γ v k = (((H - γ • 1) ^ k) v) := by

  induction k with
  | zero => simp [noInversionSeq]
  | succ k ih =>
    rw [noInversionSeq, ih, pow_succ']
    rfl

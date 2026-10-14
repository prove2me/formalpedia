-- Prove2me | solution 1 for BookProof.ChapterH5.krylovSpan_shift_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:59:11.269297+00:00
-- url     : https://prove2.me/submissions/046ea731-f165-4a3a-80d3-6e332a7f80a3

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.krylovSpan_shift_eq
import Mathlib
import Definitions.Def_ChapterH5
import Theorems.Thm_BookProof_ChapterH5_krylovSpan_shift_le
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) :
    krylovSpan (H - γ • 1) v m = krylovSpan H v m := by

  refine le_antisymm (krylovSpan_shift_le H γ v m) ?_
  have hback : (H - γ • 1) - (-γ) • (1 : E →ₗ[K] E) = H := by
    rw [neg_smul, sub_neg_eq_add, sub_add_cancel]
  have := krylovSpan_shift_le (H - γ • 1) (-γ) v m
  rwa [hback] at this

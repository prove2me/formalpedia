-- Prove2me | solution 1 for BookProof.ChapterH5.krylovSpan_map_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:36:12.175308+00:00
-- url     : https://prove2.me/submissions/139a1df6-d01c-4bd5-8e66-921e8c7b2831

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.krylovSpan_map_le
import Mathlib
import Definitions.Def_ChapterH5
import Theorems.Thm_BookProof_ChapterH5_pow_apply_mem_krylovSpan
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) :
    Submodule.map H (krylovSpan H v m) ≤ krylovSpan H v (m + 1) := by

  rw [Submodule.map_le_iff_le_comap, krylovSpan]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, hi, rfl⟩
  have : H ((H ^ i) v) = (H ^ (i + 1)) v := by
    rw [pow_succ']
    rfl
  have hx : H ((H ^ i) v) ∈ krylovSpan H v (m + 1) := by
    rw [this]
    exact pow_apply_mem_krylovSpan (Nat.succ_lt_succ hi)
  exact hx

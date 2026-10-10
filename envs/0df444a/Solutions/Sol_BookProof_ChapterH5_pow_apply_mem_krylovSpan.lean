-- Prove2me | solution 1 for BookProof.ChapterH5.pow_apply_mem_krylovSpan
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:35:27.964109+00:00
-- url     : https://prove2.me/submissions/f26c3060-ca18-459a-9ef0-ebb4a762b8f0

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.pow_apply_mem_krylovSpan
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution {i m : ℕ} (hi : i < m) :
    (H ^ i) v ∈ krylovSpan H v m := Submodule.subset_span ⟨i, hi, rfl⟩

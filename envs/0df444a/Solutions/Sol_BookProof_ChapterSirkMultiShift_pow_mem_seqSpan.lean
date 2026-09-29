-- Prove2me | solution 1 for BookProof.ChapterSirkMultiShift.pow_mem_seqSpan
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:34:41.194216+00:00
-- url     : https://prove2.me/submissions/197bd4df-9af3-4264-a12d-504a35bec8ee

-- Generated from ChapterSirkMultiShift.lean — solution of BookProof.ChapterSirkMultiShift.pow_mem_seqSpan
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
import Theorems.Thm_BookProof_ChapterSirkMultiShift_mem_seqSpan
import Theorems.Thm_BookProof_ChapterSirkMultiShift_seqSpan_mono
open BookProof.ChapterSirkMultiShift











noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (u : ℕ → E)
    (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (i : ℕ) :
    (H ^ i) v ∈ seqSpan (K := K) u (i + 1) := by

  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hlow : krylovSpan H v i ≤ seqSpan (K := K) u (i + 1) := by
      refine Submodule.span_le.mpr ?_
      rintro x ⟨j, hj, rfl⟩
      exact seqSpan_mono u (by omega) (ih j hj)
    have h1 : u i ∈ seqSpan (K := K) u (i + 1) := mem_seqSpan u (Nat.lt_succ_self i)
    have h2 : u i - (H ^ i) v ∈ seqSpan (K := K) u (i + 1) := hlow (hu i)
    have : (H ^ i) v = u i - (u i - (H ^ i) v) := by abel
    rw [this]
    exact Submodule.sub_mem _ h1 h2

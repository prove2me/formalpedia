-- Prove2me | solution 1 for BookProof.ChapterSirkMultiShift.mem_seqSpan
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:46:28.716129+00:00
-- url     : https://prove2.me/submissions/f3e7c3aa-6eba-40df-be22-a777574f22f0

-- Generated from ChapterSirkMultiShift.lean — solution of BookProof.ChapterSirkMultiShift.mem_seqSpan
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift











noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

set_option maxHeartbeats 1000000 in
theorem solution (u : ℕ → E) {i m : ℕ} (hi : i < m) :
    u i ∈ seqSpan (K := K) u m := Submodule.subset_span ⟨i, hi, rfl⟩

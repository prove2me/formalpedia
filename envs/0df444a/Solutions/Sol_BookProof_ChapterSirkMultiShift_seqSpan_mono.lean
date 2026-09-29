-- Prove2me | solution 1 for BookProof.ChapterSirkMultiShift.seqSpan_mono
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:52:20.566253+00:00
-- url     : https://prove2.me/submissions/2633320b-0afb-464e-945d-78c87fc95ef0

-- Generated from ChapterSirkMultiShift.lean — solution of BookProof.ChapterSirkMultiShift.seqSpan_mono
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift











noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

set_option maxHeartbeats 1000000 in
theorem solution (u : ℕ → E) {m n : ℕ} (hmn : m ≤ n) :
    seqSpan (K := K) u m ≤ seqSpan (K := K) u n := Submodule.span_mono fun _ ⟨i, hi, hx⟩ => ⟨i, lt_of_lt_of_le hi hmn, hx⟩

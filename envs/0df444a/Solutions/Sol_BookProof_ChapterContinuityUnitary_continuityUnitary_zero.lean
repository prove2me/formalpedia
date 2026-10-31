-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.continuityUnitary_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:38:50.349768+00:00
-- url     : https://prove2.me/submissions/b0d34dfc-953c-4fb1-b502-56a0a9fe96d8

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]

open scoped BigOperators Matrix TensorProduct

theorem solution (v : ZMod N → ℝ) : continuityUnitary v 0 = 1 := by
  simp only [continuityUnitary]
  simp [zero_mul, zero_smul, NormedSpace.exp_zero]

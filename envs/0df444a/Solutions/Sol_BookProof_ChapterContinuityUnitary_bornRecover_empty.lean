-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.bornRecover_empty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:42:32.336593+00:00
-- url     : https://prove2.me/submissions/f7c227a5-b2aa-486f-afbb-c0b5c5b0d864

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornRecover_empty
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct


theorem solution (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ) :
    bornRecover v t psi ∅ = 0 := by
  simp [bornRecover]


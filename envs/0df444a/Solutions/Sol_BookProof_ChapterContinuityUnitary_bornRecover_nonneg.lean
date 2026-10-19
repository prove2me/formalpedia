-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.bornRecover_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:42:45.303978+00:00
-- url     : https://prove2.me/submissions/dacba9d5-3ae9-4a1f-b7d2-73ac9dcb0e63

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornRecover_nonneg
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct


theorem solution (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ)
    (B : Finset (ZMod N)) : 0 ≤ bornRecover v t psi B := by
  unfold bornRecover
  positivity


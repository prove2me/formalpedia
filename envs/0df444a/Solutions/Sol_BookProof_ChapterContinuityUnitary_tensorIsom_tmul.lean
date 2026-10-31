-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.tensorIsom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:41:23.660919+00:00
-- url     : https://prove2.me/submissions/3a5255b4-99db-4f33-b6cf-bf2772c5ea0e

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]

open scoped BigOperators Matrix TensorProduct

theorem solution (X Z : Type*) [Fintype Z] [DecidableEq Z]
    (f : X → ℂ) (g : Z → ℂ) :
    tensorIsom X Z (f ⊗ₜ g) = fun p => f p.1 * g p.2 := by
  funext p
  simp [tensorIsom, LinearEquiv.trans_apply, swapCurry, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, mul_comm]

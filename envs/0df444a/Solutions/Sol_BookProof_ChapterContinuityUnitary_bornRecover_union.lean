-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.bornRecover_union
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:38:53.71104+00:00
-- url     : https://prove2.me/submissions/913e075f-a58d-41c7-aac5-cd3f6d77816c

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]

open scoped BigOperators Matrix TensorProduct

theorem solution (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ)
    {B C : Finset (ZMod N)} (h : Disjoint B C) :
    bornRecover v t psi (B ∪ C) = bornRecover v t psi B + bornRecover v t psi C := by
  simp only [bornRecover]
  exact Finset.sum_union h

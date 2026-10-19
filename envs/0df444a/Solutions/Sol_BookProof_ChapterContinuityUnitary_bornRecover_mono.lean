-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.bornRecover_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:42:59.904412+00:00
-- url     : https://prove2.me/submissions/11b10f60-3c47-4e54-b7ed-b0c45fc84e24

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornRecover_mono
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct


theorem solution (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ)
    {B C : Finset (ZMod N)} (h : B ⊆ C) :
    bornRecover v t psi B ≤ bornRecover v t psi C := by
  unfold bornRecover
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => by positivity)


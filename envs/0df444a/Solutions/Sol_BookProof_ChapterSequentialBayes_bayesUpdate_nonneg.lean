-- Prove2me | solution 1 for BookProof.ChapterSequentialBayes.bayesUpdate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:58.385966+00:00
-- url     : https://prove2.me/submissions/8a92fefc-180f-4638-9b29-92d4a24db29e

-- Generated from ChapterSequentialBayes.lean — solution of BookProof.ChapterSequentialBayes.bayesUpdate_nonneg
import Mathlib
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterSequentialBayes



open scoped BigOperators


variable {X : Type*} [Fintype X]

variable {X : Type*} [Fintype X]

set_option maxHeartbeats 1000000 in
theorem solution {prior ℓ : X → ℝ} (hprior : ∀ x, 0 ≤ prior x)
    (hℓ : ∀ x, 0 ≤ ℓ x) (x : X) : 0 ≤ bayesUpdate prior ℓ x := by

  unfold bayesUpdate
  apply div_nonneg (mul_nonneg (hprior x) (hℓ x))
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hprior i) (hℓ i)

-- Prove2me | solution 1 for BookProof.ChapterSequentialBayes.bayesUpdate_evidence
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:31:00.565179+00:00
-- url     : https://prove2.me/submissions/3d0fddf7-bc6a-4536-9ac2-89dc6f3acb17

-- Generated from ChapterSequentialBayes.lean — solution of BookProof.ChapterSequentialBayes.bayesUpdate_evidence
import Mathlib
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterSequentialBayes



open scoped BigOperators


variable {X : Type*} [Fintype X]

variable {X : Type*} [Fintype X]

set_option maxHeartbeats 1000000 in
theorem solution {prior ℓ₁ ℓ₂ : X → ℝ} :
    (∑ x, bayesUpdate prior ℓ₁ x * ℓ₂ x)
      = (∑ x, prior x * (ℓ₁ x * ℓ₂ x)) / (∑ x, prior x * ℓ₁ x) := by

  unfold bayesUpdate
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun x _ => by ring)

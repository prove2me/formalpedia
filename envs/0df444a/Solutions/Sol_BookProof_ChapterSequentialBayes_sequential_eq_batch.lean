-- Prove2me | solution 1 for BookProof.ChapterSequentialBayes.sequential_eq_batch
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:31:01.552756+00:00
-- url     : https://prove2.me/submissions/b492f838-1043-4880-b3bf-884e348a8051

-- Generated from ChapterSequentialBayes.lean — solution of BookProof.ChapterSequentialBayes.sequential_eq_batch
import Mathlib
import Definitions.Def_ChapterSequentialBayes
import Theorems.Thm_BookProof_ChapterSequentialBayes_bayesUpdate_evidence
open BookProof.ChapterSequentialBayes



open scoped BigOperators


variable {X : Type*} [Fintype X]

variable {X : Type*} [Fintype X]

set_option maxHeartbeats 1000000 in
theorem solution {prior ℓ₁ ℓ₂ : X → ℝ}
    (h1 : 0 < totEvidence prior ℓ₁)
    (h2 : 0 < totEvidence prior (fun x => ℓ₁ x * ℓ₂ x)) :
    bayesUpdate (bayesUpdate prior ℓ₁) ℓ₂ = bayesUpdate prior (fun x => ℓ₁ x * ℓ₂ x) := by

  have hZ1 : (∑ x', prior x' * ℓ₁ x') ≠ 0 := ne_of_gt h1
  have hZc : (∑ x', prior x' * (ℓ₁ x' * ℓ₂ x')) ≠ 0 := ne_of_gt h2
  funext x
  have hstep : bayesUpdate (bayesUpdate prior ℓ₁) ℓ₂ x
      = bayesUpdate prior ℓ₁ x * ℓ₂ x / (∑ x', bayesUpdate prior ℓ₁ x' * ℓ₂ x') := rfl
  rw [hstep, bayesUpdate_evidence]
  unfold bayesUpdate
  field_simp

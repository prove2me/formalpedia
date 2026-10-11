-- Prove2me | solution 1 for BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:31:03.498097+00:00
-- url     : https://prove2.me/submissions/cd64ad24-0f70-4eed-9514-5c89f8bdc709

-- Generated from ChapterSequentialBayes.lean — solution of BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch
import Mathlib
import Definitions.Def_ChapterSequentialBayes
import Theorems.Thm_BookProof_ChapterSequentialBayes_sequential_eq_batch
import Theorems.Thm_BookProof_ChapterSequentialBayes_posterior_eq_bayesUpdate
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterSequentialBayes



open scoped BigOperators


variable {X : Type*} [Fintype X]

variable {X : Type*} [Fintype X]

set_option maxHeartbeats 1000000 in
theorem solution {Y₁ Y₂ : Type*}
    (prior : X → ℝ) (L₁ : X → Y₁ → ℝ) (L₂ : X → Y₂ → ℝ) (y₁ : Y₁) (y₂ : Y₂)
    (h1 : 0 < totEvidence prior (fun x => L₁ x y₁))
    (h2 : 0 < totEvidence prior (fun x => L₁ x y₁ * L₂ x y₂)) :
    bayesUpdate (BookProof.ChapterBayesInference.posterior prior L₁ y₁) (fun x => L₂ x y₂)
      = bayesUpdate prior (fun x => L₁ x y₁ * L₂ x y₂) := by

  rw [posterior_eq_bayesUpdate]
  exact sequential_eq_batch h1 h2

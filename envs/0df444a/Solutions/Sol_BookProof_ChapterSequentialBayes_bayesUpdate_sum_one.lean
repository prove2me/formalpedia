-- Prove2me | solution 1 for BookProof.ChapterSequentialBayes.bayesUpdate_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:59.527354+00:00
-- url     : https://prove2.me/submissions/7343aaf1-04cb-4dc9-8019-e3bc67787105

-- Generated from ChapterSequentialBayes.lean — solution of BookProof.ChapterSequentialBayes.bayesUpdate_sum_one
import Mathlib
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterSequentialBayes



open scoped BigOperators


variable {X : Type*} [Fintype X]

variable {X : Type*} [Fintype X]

set_option maxHeartbeats 1000000 in
theorem solution {prior ℓ : X → ℝ} (hpos : 0 < totEvidence prior ℓ) :
    ∑ x, bayesUpdate prior ℓ x = 1 := by

  unfold bayesUpdate
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

-- Prove2me | solution 1 for BookProof.ChapterSequentialBayes.posterior_eq_bayesUpdate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:31:02.506324+00:00
-- url     : https://prove2.me/submissions/28c6d41d-7eb3-4e8f-a446-898858124c93

-- Generated from ChapterSequentialBayes.lean — solution of BookProof.ChapterSequentialBayes.posterior_eq_bayesUpdate
import Mathlib
import Definitions.Def_ChapterSequentialBayes
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterSequentialBayes



open scoped BigOperators


variable {X : Type*} [Fintype X]

variable {X : Type*} [Fintype X]

set_option maxHeartbeats 1000000 in
theorem solution {Y : Type*}
    (prior : X → ℝ) (L : X → Y → ℝ) (y : Y) :
    BookProof.ChapterBayesInference.posterior prior L y = bayesUpdate prior (fun x => L x y) := by

  funext x
  rfl

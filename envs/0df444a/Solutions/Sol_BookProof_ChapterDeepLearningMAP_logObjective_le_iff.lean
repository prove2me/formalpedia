-- Prove2me | solution 1 for BookProof.ChapterDeepLearningMAP.logObjective_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:48:17.506118+00:00
-- url     : https://prove2.me/submissions/93c3cc5e-cded-44ba-a6ab-47ca4f54a234

-- Generated from ChapterDeepLearningMAP.lean — solution of BookProof.ChapterDeepLearningMAP.logObjective_le_iff
import Mathlib
import Definitions.Def_ChapterDeepLearningMAP
import Theorems.Thm_BookProof_ChapterDeepLearningMAP_exp_logObjective
open BookProof.ChapterDeepLearningMAP




variable {Model Data : Type*}

variable {Model Data : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (prior : Model → ℝ)
    (likelihood : Model → Data → ℝ) (d : Data)
    (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d)
    (a b : Model) :
    logObjective prior likelihood d a ≤ logObjective prior likelihood d b ↔
      posteriorWeight prior likelihood d a ≤ posteriorWeight prior likelihood d b := by

  rw [← exp_logObjective _ _ _ hprior hlike,
    ← exp_logObjective _ _ _ hprior hlike, Real.exp_le_exp]

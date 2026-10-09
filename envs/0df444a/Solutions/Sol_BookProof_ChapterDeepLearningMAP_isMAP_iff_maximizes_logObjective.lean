-- Prove2me | solution 1 for BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:48:43.14799+00:00
-- url     : https://prove2.me/submissions/b9fc0e8a-1b94-4212-81bf-ee62a05569f5

-- Generated from ChapterDeepLearningMAP.lean — solution of BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective
import Mathlib
import Definitions.Def_ChapterDeepLearningMAP
import Theorems.Thm_BookProof_ChapterDeepLearningMAP_logObjective_le_iff
import Theorems.Thm_BookProof_ChapterDeepLearningMAP_posterior_le_iff_weight
open BookProof.ChapterDeepLearningMAP




variable {Model Data : Type*}

variable {Model Data : Type*}
variable [Fintype Model]

set_option maxHeartbeats 1000000 in
theorem solution (prior : Model → ℝ)
    (likelihood : Model → Data → ℝ) (d : Data)
    (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d)
    (hevidence : 0 < BookProof.ChapterBayesInference.evidence prior likelihood d)
    (best : Model) :
    (∀ m, BookProof.ChapterBayesInference.posterior prior likelihood d m ≤
      BookProof.ChapterBayesInference.posterior prior likelihood d best) ↔
    (∀ m, logObjective prior likelihood d m ≤
      logObjective prior likelihood d best) := by

  constructor
  · intro h m
    exact (logObjective_le_iff prior likelihood d hprior hlike m best).mpr
      ((posterior_le_iff_weight prior likelihood d hevidence m best).mp (h m))
  · intro h m
    apply (posterior_le_iff_weight prior likelihood d hevidence m best).mpr
    exact (logObjective_le_iff prior likelihood d hprior hlike m best).mp (h m)

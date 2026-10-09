-- Prove2me | solution 1 for BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:48:30.220828+00:00
-- url     : https://prove2.me/submissions/3dce6e9d-1e0d-4ddd-9c1c-2c2ab11ace19

-- Generated from ChapterDeepLearningMAP.lean — solution of BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight
import Mathlib
import Definitions.Def_ChapterDeepLearningMAP
import Definitions.Def_ChapterBayesInference
open BookProof
open BookProof.ChapterBayesInference
open BookProof.ChapterDeepLearningMAP




variable {Model Data : Type*}

variable {Model Data : Type*}
variable [Fintype Model]

set_option maxHeartbeats 1000000 in
theorem solution (prior : Model → ℝ)
    (likelihood : Model → Data → ℝ) (d : Data)
    (hevidence : 0 < BookProof.ChapterBayesInference.evidence prior likelihood d)
    (a b : Model) :
    BookProof.ChapterBayesInference.posterior prior likelihood d a ≤
      BookProof.ChapterBayesInference.posterior prior likelihood d b ↔
    posteriorWeight prior likelihood d a ≤ posteriorWeight prior likelihood d b := by

  unfold ChapterBayesInference.posterior
  rw [div_le_div_iff_of_pos_right hevidence]
  rfl

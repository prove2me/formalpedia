-- Prove2me | solution 1 for BookProof.ChapterDeepLearningSampling.posterior_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:49:12.108475+00:00
-- url     : https://prove2.me/submissions/8574e725-5297-4e4d-93a0-c4446105e82e

-- Generated from ChapterDeepLearningSampling.lean — solution of BookProof.ChapterDeepLearningSampling.posterior_sum_one
import Mathlib
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterDeepLearningSampling



open scoped BigOperators


variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]








variable [Fintype Model]

variable {Seed Model Data : Type*}
variable [Fintype Seed] [DecidableEq Model]
variable [Fintype Model]

set_option maxHeartbeats 1000000 in
theorem solution (seedProb : Seed → ℝ) (train : Seed → Model)
    (likelihood : Model → Data → ℝ) (d : Data)
    (hd : 0 < evidence seedProb train likelihood d) :
    ∑ m, posterior seedProb train likelihood d m = 1 := by

  unfold posterior
  rw [← Finset.sum_div, div_eq_iff] <;> aesop

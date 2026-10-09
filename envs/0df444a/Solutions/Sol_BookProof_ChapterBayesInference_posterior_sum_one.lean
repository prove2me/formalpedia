-- Prove2me | solution 1 for BookProof.ChapterBayesInference.posterior_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:26:34.486951+00:00
-- url     : https://prove2.me/submissions/d76ada25-8645-4142-8733-7b4b50cccca9

-- Generated from ChapterBayesInference.lean — solution of BookProof.ChapterBayesInference.posterior_sum_one
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference



open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
variable {prior : X → ℝ} {L : X → Y → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (y : Y) (hy : 0 < evidence prior L y) :
    ∑ x, posterior prior L y x = 1 := by

  convert div_self hy.ne';
  unfold posterior evidence; simp [ Finset.sum_div _ _ _ ] ;

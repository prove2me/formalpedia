-- Prove2me | solution 1 for BookProof.ChapterBayesInference.joint_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:26:29.41221+00:00
-- url     : https://prove2.me/submissions/4b04f92d-80c6-4f8d-9a42-43495b56962e

-- Generated from ChapterBayesInference.lean — solution of BookProof.ChapterBayesInference.joint_sum_one
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference



open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
variable {prior : X → ℝ} {L : X → Y → ℝ}

set_option maxHeartbeats 1000000 in
omit [DecidableEq X] [DecidableEq Y] in
theorem solution (hprior_sum : ∑ x, prior x = 1) (hL_row : ∀ x, ∑ y, L x y = 1) :
    ∑ x, ∑ y, joint prior L x y = 1 := by

  simp_all [ joint, ← Finset.mul_sum _ _ _ ]

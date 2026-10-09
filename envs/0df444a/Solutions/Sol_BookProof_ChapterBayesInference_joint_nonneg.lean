-- Prove2me | solution 1 for BookProof.ChapterBayesInference.joint_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:26:28.329778+00:00
-- url     : https://prove2.me/submissions/9ab22469-e130-42a3-ae58-81038b33ee0b

-- Generated from ChapterBayesInference.lean — solution of BookProof.ChapterBayesInference.joint_nonneg
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference



open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
variable {prior : X → ℝ} {L : X → Y → ℝ}

set_option maxHeartbeats 1000000 in
omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem solution (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y)
    (x : X) (y : Y) : 0 ≤ joint prior L x y := by

  exact mul_nonneg ( hprior x ) ( hL x y )

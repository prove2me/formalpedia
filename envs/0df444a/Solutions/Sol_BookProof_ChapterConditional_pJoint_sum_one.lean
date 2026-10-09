-- Prove2me | solution 1 for BookProof.ChapterConditional.pJoint_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:42:34.156148+00:00
-- url     : https://prove2.me/submissions/1052a54f-b4e8-4e21-9c5c-679c2d83c503

-- Generated from ChapterConditional.lean — solution of BookProof.ChapterConditional.pJoint_sum_one
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional



open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]

set_option maxHeartbeats 1000000 in
theorem solution (B : Matrix Y X 𝕜)
    (hB : ∑ x, ∑ y, ‖B y x‖ ^ 2 = 1) :
    ∑ x, ∑ y, pJoint B x y = 1 := by

  exact hB
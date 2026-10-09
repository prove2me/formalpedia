-- Prove2me | solution 1 for BookProof.ChapterConditional.pMarg_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:42:35.353182+00:00
-- url     : https://prove2.me/submissions/c2e24be5-19d8-4ab7-b2df-9575b660f8d6

-- Generated from ChapterConditional.lean — solution of BookProof.ChapterConditional.pMarg_sum_one
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
    ∑ x, pMarg B x = 1 := by

  simp only [pMarg]
  exact hB

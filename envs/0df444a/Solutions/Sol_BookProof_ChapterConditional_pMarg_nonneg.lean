-- Prove2me | solution 1 for BookProof.ChapterConditional.pMarg_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:41:42.055368+00:00
-- url     : https://prove2.me/submissions/3f09e7f3-ce74-4953-8a10-325f9de39d7a

-- Generated from ChapterConditional.lean — solution of BookProof.ChapterConditional.pMarg_nonneg
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
omit [Fintype X] [DecidableEq X] in
theorem solution (B : Matrix Y X 𝕜) (x : X) : 0 ≤ pMarg B x := by

  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

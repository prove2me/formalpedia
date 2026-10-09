-- Prove2me | solution 1 for BookProof.ChapterConditional.pJoint_eq_cond_mul_marg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:43:15.137676+00:00
-- url     : https://prove2.me/submissions/b8d13ac7-a091-4efe-871d-36dcd1bfb2c6

-- Generated from ChapterConditional.lean — solution of BookProof.ChapterConditional.pJoint_eq_cond_mul_marg
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
theorem solution (B : Matrix Y X 𝕜) (x : X) (y : Y)
    (hx : 0 < pMarg B x) :
    pJoint B x y = pCond B x y * pMarg B x := by

  simp_all [ pCond, div_mul_cancel₀ _ hx.ne' ]

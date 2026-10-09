-- Prove2me | solution 1 for BookProof.ChapterConditional.pCond_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:43:14.20837+00:00
-- url     : https://prove2.me/submissions/8458212e-8449-467c-8e5e-2e3fc4583b99

-- Generated from ChapterConditional.lean — solution of BookProof.ChapterConditional.pCond_sum_one
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
theorem solution (B : Matrix Y X 𝕜) (x : X) (hx : 0 < pMarg B x) :
    ∑ y, pCond B x y = 1 := by

  unfold pCond;
  rw [ ← Finset.sum_div, div_eq_iff ] <;> aesop

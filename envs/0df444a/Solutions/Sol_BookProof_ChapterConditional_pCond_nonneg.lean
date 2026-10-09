-- Prove2me | solution 1 for BookProof.ChapterConditional.pCond_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:42:36.414+00:00
-- url     : https://prove2.me/submissions/860518bf-6d62-4fb9-90a7-8d3df3352025

-- Generated from ChapterConditional.lean — solution of BookProof.ChapterConditional.pCond_nonneg
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
theorem solution (B : Matrix Y X 𝕜) (x : X) (y : Y) : 0 ≤ pCond B x y := by

  exact div_nonneg ( sq_nonneg _ ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ )

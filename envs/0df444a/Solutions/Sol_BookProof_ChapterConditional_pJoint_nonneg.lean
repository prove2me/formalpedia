-- Prove2me | solution 1 for BookProof.ChapterConditional.pJoint_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:47:42.0505+00:00
-- url     : https://prove2.me/submissions/69a04baf-57e5-4901-8821-6d6b3840d056

-- Generated from ChapterConditional.lean — theorem BookProof.ChapterConditional.pJoint_nonneg
import Mathlib
import Definitions.Def_ChapterConditional
open BookProof.ChapterConditional


open scoped BigOperators Matrix
open Finset


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
variable {𝕜 : Type*} [RCLike 𝕜]
open BookProof.ChapterConditional

theorem solution(B : Matrix Y X 𝕜) (x : X) (y : Y) : 0 ≤ pJoint B x y := by
  unfold pJoint
  positivity

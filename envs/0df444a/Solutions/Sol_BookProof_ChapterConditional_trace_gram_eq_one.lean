-- Prove2me | solution 1 for BookProof.ChapterConditional.trace_gram_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:41:56.997151+00:00
-- url     : https://prove2.me/submissions/e8ff2f53-dd03-4b19-a25f-a766fd30cea7

-- Generated from ChapterConditional.lean — solution of BookProof.ChapterConditional.trace_gram_eq_one
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
    (Bᴴ * B).trace = ((1 : ℝ) : 𝕜) := by

  rw [ ← hB ] ; simp [ Matrix.trace, Matrix.mul_apply ] ; ring;
  simp [ mul_comm, RCLike.mul_conj ]

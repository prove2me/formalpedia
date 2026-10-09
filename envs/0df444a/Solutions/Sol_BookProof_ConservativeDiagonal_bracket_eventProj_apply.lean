-- Prove2me | solution 1 for BookProof.ConservativeDiagonal.bracket_eventProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:44:33.556251+00:00
-- url     : https://prove2.me/submissions/6501edfb-001f-4287-99cb-14da7d4b88db

-- Generated from ChapterConservativeDiagonal.lean — solution of BookProof.ConservativeDiagonal.bracket_eventProj_apply
import Mathlib
import Definitions.Def_ChapterConservativeDiagonal
open BookProof.ConservativeDiagonal



open scoped Matrix
open Matrix BookProof.FreeFieldConstraint


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (S : Finset n) (k l : n) :
    bracket H (eventProj S) k l
      = H k l * ((if l ∈ S then (1 : ℂ) else 0) - (if k ∈ S then (1 : ℂ) else 0)) := by

  simp only [bracket, eventProj, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

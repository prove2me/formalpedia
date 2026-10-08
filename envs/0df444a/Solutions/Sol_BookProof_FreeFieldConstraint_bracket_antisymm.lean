-- Prove2me | solution 1 for BookProof.FreeFieldConstraint.bracket_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T12:04:42.355742+00:00
-- url     : https://prove2.me/submissions/b86f49b2-21f2-4a5e-ad51-3612dea9cfa4

-- Generated from ChapterFreeFieldConstraint.lean — solution of BookProof.FreeFieldConstraint.bracket_antisymm
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint




variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (a b : R) : bracket a b = - bracket b a := by

  simp only [bracket]; abel

-- Prove2me | solution 1 for BookProof.FreeFieldConstraint.bracket_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T12:17:45.500334+00:00
-- url     : https://prove2.me/submissions/1479cfce-feb8-4936-bda6-9805520ed912

-- Generated from ChapterFreeFieldConstraint.lean — solution of BookProof.FreeFieldConstraint.bracket_jacobi
import Mathlib
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.FreeFieldConstraint




variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (a b c : R) :
    bracket (bracket a b) c + bracket (bracket b c) a + bracket (bracket c a) b = 0 := by

  simp only [bracket]; noncomm_ring

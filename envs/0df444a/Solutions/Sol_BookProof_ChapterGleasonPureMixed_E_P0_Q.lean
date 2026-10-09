-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.E_P0_Q
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:47:25.971116+00:00
-- url     : https://prove2.me/submissions/2df7d181-1d90-4b79-820b-9b759f02fada

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.E_P0_Q
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : E P0 Q = 1/2 := by

  simp [E, Q, P0, Matrix.trace, Fin.sum_univ_two]

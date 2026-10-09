-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.P0_Q_not_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:46:43.63778+00:00
-- url     : https://prove2.me/submissions/f8e5c86c-2bb8-443d-ad59-54ef5345c3fd

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.P0_Q_not_commute
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : P0 * Q ≠ Q * P0 := by

  intro h
  have := congrFun (congrFun h 0) 1
  simp [P0, Q, Matrix.mul_apply, Fin.sum_univ_two] at this

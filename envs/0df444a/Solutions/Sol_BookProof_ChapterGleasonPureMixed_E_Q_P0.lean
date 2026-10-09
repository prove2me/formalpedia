-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.E_Q_P0
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:47:24.940921+00:00
-- url     : https://prove2.me/submissions/aa98a6ac-67fe-47c7-86e1-1e2bb8c80c5f

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.E_Q_P0
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : E Q P0 = 1/2 := by

  simp [E, Q, P0, Matrix.trace, Fin.sum_univ_two]

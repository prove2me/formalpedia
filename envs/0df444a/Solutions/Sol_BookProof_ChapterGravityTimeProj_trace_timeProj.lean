-- Prove2me | solution 1 for BookProof.ChapterGravityTimeProj.trace_timeProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:33:02.968989+00:00
-- url     : https://prove2.me/submissions/6d9b0b1f-f54a-4dd0-8063-793c5b9340a3

-- Generated from ChapterGravityTimeProj.lean — solution of BookProof.ChapterGravityTimeProj.trace_timeProj
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityTimeProj




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (timeProj v).trace = 1 := by

  unfold timeProj; simp only [trace, diag_apply, of_apply, Finset.sum_neg_distrib] ; ring;
  linarith!

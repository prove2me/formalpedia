-- Prove2me | solution 1 for BookProof.ChapterA3.hasAdLambda_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:07:06.807247+00:00
-- url     : https://prove2.me/submissions/ae91a3cb-26c1-46d0-90a2-5e94a76cf2d5

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.hasAdLambda_zero
import Mathlib
import Definitions.Def_ChapterA3e
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : HasAdLambda (0 : Matrix (Fin 4) (Fin 4) ℝ) 0 := by

  intro μ; simp

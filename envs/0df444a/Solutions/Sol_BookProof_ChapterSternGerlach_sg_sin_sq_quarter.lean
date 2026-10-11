-- Prove2me | solution 1 for BookProof.ChapterSternGerlach.sg_sin_sq_quarter
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:01:02.007988+00:00
-- url     : https://prove2.me/submissions/038ff75b-2a72-4fe2-bbf4-d49b1333a02d

-- Generated from ChapterSternGerlach.lean — solution of BookProof.ChapterSternGerlach.sg_sin_sq_quarter
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach




open Complex Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by

  rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

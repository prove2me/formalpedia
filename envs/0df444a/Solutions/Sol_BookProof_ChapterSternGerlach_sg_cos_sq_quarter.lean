-- Prove2me | solution 1 for BookProof.ChapterSternGerlach.sg_cos_sq_quarter
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:00:14.099582+00:00
-- url     : https://prove2.me/submissions/7ae7e751-59c7-46e7-b502-864571e979f1

-- Generated from ChapterSternGerlach.lean — solution of BookProof.ChapterSternGerlach.sg_cos_sq_quarter
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach




open Complex Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by

  rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

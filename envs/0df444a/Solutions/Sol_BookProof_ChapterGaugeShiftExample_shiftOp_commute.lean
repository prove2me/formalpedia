-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.shiftOp_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:37:15.108981+00:00
-- url     : https://prove2.me/submissions/f3c44042-6cb5-4d50-b08e-fac45a125f60

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.shiftOp_commute
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_shiftOp_mul
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution (m n : ℤ) : shiftOp m * shiftOp n = shiftOp n * shiftOp m := by

  rw [shiftOp_mul, shiftOp_mul, add_comm]

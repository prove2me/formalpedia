-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.shiftOp_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:37:28.00699+00:00
-- url     : https://prove2.me/submissions/1dfb95f7-7545-4c82-b3f8-0fe820032771

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.shiftOp_adjoint
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution (m : ℤ) :
    ContinuousLinearMap.adjoint (shiftOp m) = shiftOp (-m) := by

  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  have h := inner_shiftOp_left (-m) f g
  simpa using h

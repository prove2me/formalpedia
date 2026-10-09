-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.velocityOp_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:39:21.605423+00:00
-- url     : https://prove2.me/submissions/6639d6b8-5b7f-4adf-87b0-9f212550d5cd

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.velocityOp_commute
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution (v w : LinfZ) :
    velocityOp v * velocityOp w = velocityOp w * velocityOp v := by

  ext f k
  simp only [ContinuousLinearMap.mul_apply, velocityOp_apply]
  ring

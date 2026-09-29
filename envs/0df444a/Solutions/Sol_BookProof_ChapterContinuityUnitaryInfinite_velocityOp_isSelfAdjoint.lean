-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.velocityOp_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:14:36.212093+00:00
-- url     : https://prove2.me/submissions/1d4cbcd0-e7a8-41b2-91fb-42853fa6725e

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.velocityOp_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) : IsSelfAdjoint (velocityOp v) := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (velocityOp_isSymmetric v)

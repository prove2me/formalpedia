-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.momentum_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:10:46.994719+00:00
-- url     : https://prove2.me/submissions/628d20a4-ef71-40f7-8bf6-f6f248c3554e

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.momentum_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution : IsSelfAdjoint momentum := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 momentum_isSymmetric

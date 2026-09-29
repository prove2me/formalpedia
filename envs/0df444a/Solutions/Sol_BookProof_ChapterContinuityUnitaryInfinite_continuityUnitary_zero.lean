-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:07:46.050174+00:00
-- url     : https://prove2.me/submissions/b46fee05-a2ed-4db1-9f9d-018a11f23799

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_zero
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) : continuityUnitary v 0 = 1 := by

  simp [continuityUnitary]

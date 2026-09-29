-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.bornRecover_empty
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T05:07:35.670287+00:00
-- url     : https://prove2.me/submissions/d158171a-0c49-4e7e-b099-2d2a56046db0

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.bornRecover_empty
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) (t : ℝ) (psi : L2Z) : bornRecover v t psi ∅ = 0 := by

  simp [bornRecover]

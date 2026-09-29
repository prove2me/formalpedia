-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.bornRecover_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T05:10:46.87261+00:00
-- url     : https://prove2.me/submissions/8aca4459-a8fc-425c-a24d-1f802f727094

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.bornRecover_nonneg
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) (t : ℝ) (psi : L2Z) (B : Finset ℤ) :
    0 ≤ bornRecover v t psi B := Finset.sum_nonneg fun _ _ => by positivity

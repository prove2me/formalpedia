-- Prove2me | solution 2 for BookProof.ChapterContinuityUnitaryInfinite.bornRecover_union
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:04:33.451034+00:00
-- url     : https://prove2.me/submissions/b858a061-e3b5-40ad-bb87-9effe0b03e31

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.bornRecover_union
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) (t : ℝ) (psi : L2Z) {B C : Finset ℤ}
    (h : Disjoint B C) :
    bornRecover v t psi (B ∪ C) = bornRecover v t psi B + bornRecover v t psi C := by

  simp [bornRecover, Finset.sum_union h]

-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.bornRecover_union
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T05:12:38.550154+00:00
-- url     : https://prove2.me/submissions/6eec9ecc-d217-4aab-89fd-945d7a010172

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

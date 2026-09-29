-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.bornRecover_mono
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T05:08:55.498167+00:00
-- url     : https://prove2.me/submissions/bb59e156-a4ea-4763-8cba-4cb9e2d5bdb3

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.bornRecover_mono
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) (t : ℝ) (psi : L2Z) {B C : Finset ℤ} (h : B ⊆ C) :
    bornRecover v t psi B ≤ bornRecover v t psi C := Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.shiftOp_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:18.731441+00:00
-- url     : https://prove2.me/submissions/2e4e71ff-6377-4b9b-a4df-ba0700a30434

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.shiftOp_unitary
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_shiftOp_mul
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_shiftOp_adjoint
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite


@[simp] private theorem shiftOp_zero : shiftOp 0 = (1 : L2Z →L[ℂ] L2Z) := by
  ext f k
  change ((shiftOp 0 f : L2Z) : ℤ → ℂ) k = ((f : L2Z) : ℤ → ℂ) k
  simp











set_option maxHeartbeats 1000000 in

theorem solution (m : ℤ) : shiftOp m ∈ unitary (L2Z →L[ℂ] L2Z) := by
  constructor <;>
    simp only [ContinuousLinearMap.star_eq_adjoint, shiftOp_adjoint,
      shiftOp_mul, neg_add_cancel, add_neg_cancel, shiftOp_zero]

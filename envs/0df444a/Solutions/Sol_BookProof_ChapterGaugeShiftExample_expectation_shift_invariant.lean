-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.expectation_shift_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:37:43.631773+00:00
-- url     : https://prove2.me/submissions/53b244f3-a40a-4686-bb5e-d56e62848d21

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.expectation_shift_invariant
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution {A : L2Z →L[ℂ] L2Z}
    (hA : ∀ m : ℤ, A * shiftOp m = shiftOp m * A) (m : ℤ) (f : L2Z) :
    ⟪shiftOp m f, A (shiftOp m f)⟫_ℂ = ⟪f, A f⟫_ℂ := by

  have hcomm : A (shiftOp m f) = shiftOp m (A f) := by
    have := congrArg (fun T : L2Z →L[ℂ] L2Z => T f) (hA m)
    simpa [ContinuousLinearMap.mul_apply] using this
  rw [hcomm]
  exact (shiftEquiv m).inner_map_map f (A f)

-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.shiftOp_ne_velocityOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:39:36.177338+00:00
-- url     : https://prove2.me/submissions/4a9e0832-f1d7-4e53-863b-74b8cd1e27c2

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.shiftOp_ne_velocityOp
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution {m : ℤ} (hm : m ≠ 0) (v : LinfZ) :
    shiftOp m ≠ velocityOp v := by

  intro h
  have h1 := congrArg
    (fun T : L2Z →L[ℂ] L2Z => ((T (basisVecL2 0) : L2Z) : ℤ → ℂ) (-m)) h
  simp only [shiftOp_apply, velocityOp_apply, basisVecL2] at h1
  rw [neg_add_cancel, lp.single_apply, lp.single_apply] at h1
  simp [hm] at h1

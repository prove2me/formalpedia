-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.basisVecL2_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:37:57.318892+00:00
-- url     : https://prove2.me/submissions/1783b79e-24af-4f34-a3a0-d965721dc8cd

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.basisVecL2_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution (j : ℤ) : basisVecL2 j ≠ 0 := by

  intro h
  have h1 := congrArg (fun f : L2Z => (f : ℤ → ℂ) j) h
  simp only [basisVecL2, lp.single_apply, Pi.single_apply, lp.coeFn_zero,
    Pi.zero_apply] at h1
  exact one_ne_zero h1

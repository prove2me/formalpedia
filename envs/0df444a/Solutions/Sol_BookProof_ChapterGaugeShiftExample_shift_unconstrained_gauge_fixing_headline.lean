-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.shift_unconstrained_gauge_fixing_headline
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:39:37.162899+00:00
-- url     : https://prove2.me/submissions/b395a835-f50c-4485-b3d7-cfa4b340e54e

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.shift_unconstrained_gauge_fixing_headline
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_basisVecL2_ne_zero
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_velocityOp_commute
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_velocityOp_basisVecL2
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_shiftOp_basisVecL2
import Theorems.Thm_BookProof_ChapterGaugeShiftExample_shiftOp_ne_velocityOp
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution :
    (∀ v w : LinfZ, velocityOp v * velocityOp w = velocityOp w * velocityOp v) ∧
    (∀ (v : LinfZ) (j : ℤ),
      velocityOp v (basisVecL2 j) = ((v : ℤ → ℝ) j : ℂ) • basisVecL2 j) ∧
    (∀ m : ℤ, m ≠ 0 → ∀ v : LinfZ, shiftOp m ≠ velocityOp v) ∧
    (∀ m j : ℤ, shiftOp m (basisVecL2 j) = basisVecL2 (j - m) ∧
      basisVecL2 (j - m) ≠ 0) :=
  ⟨velocityOp_commute, velocityOp_basisVecL2,
      fun _ hm => shiftOp_ne_velocityOp hm,
      fun m j => ⟨shiftOp_basisVecL2 m j, basisVecL2_ne_zero _⟩⟩

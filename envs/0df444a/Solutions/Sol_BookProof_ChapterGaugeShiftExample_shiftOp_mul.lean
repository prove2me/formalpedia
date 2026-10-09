-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.shiftOp_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:36:50.60008+00:00
-- url     : https://prove2.me/submissions/9ab53a14-4fc3-40e4-8cf1-9a8f6f0d731d

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.shiftOp_mul
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution (m n : ℤ) :
    shiftOp m * shiftOp n = shiftOp (m + n) := by

  ext f k
  change ((shiftOp m (shiftOp n f) : L2Z) : ℤ → ℂ) k
      = ((shiftOp (m + n) f : L2Z) : ℤ → ℂ) k
  simp only [shiftOp_apply]
  have hk : k + m + n = k + (m + n) := by ring
  rw [hk]

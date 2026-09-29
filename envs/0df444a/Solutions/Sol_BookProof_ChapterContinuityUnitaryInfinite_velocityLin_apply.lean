-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.velocityLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:13:16.761911+00:00
-- url     : https://prove2.me/submissions/481a1168-4a65-4e1d-9583-961061add4b8

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.velocityLin_apply
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) (f : L2Z) (k : ℤ) :
    ((velocityLin v f : L2Z) : ℤ → ℂ) k = ((v : ℤ → ℝ) k : ℂ) * (f : ℤ → ℂ) k := rfl

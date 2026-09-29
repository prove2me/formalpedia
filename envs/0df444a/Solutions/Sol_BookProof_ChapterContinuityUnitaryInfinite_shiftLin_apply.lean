-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.shiftLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:12:07.871983+00:00
-- url     : https://prove2.me/submissions/738673cb-176e-4666-8207-614c09f8c61b

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.shiftLin_apply
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (m : ℤ) (f : L2Z) (k : ℤ) :
    ((shiftLin m f : L2Z) : ℤ → ℂ) k = (f : ℤ → ℂ) (k + m) := rfl

-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:29.079179+00:00
-- url     : https://prove2.me/submissions/59744216-7ff9-4ac1-bd79-0c0a1742dc1c

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re)
    (y : E) : (z • (1 : E →L[ℂ] E) - A) ((shiftEquiv h hz).symm y) = y := (shiftEquiv h hz).apply_symm_apply y

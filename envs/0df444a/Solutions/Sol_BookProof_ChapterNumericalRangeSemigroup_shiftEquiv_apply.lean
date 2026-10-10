-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.shiftEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:27.715987+00:00
-- url     : https://prove2.me/submissions/4f50c5dc-02ab-45c4-8f2c-b5c0307390db

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.shiftEquiv_apply
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re)
    (x : E) : shiftEquiv h hz x = (z • (1 : E →L[ℂ] E) - A) x := rfl

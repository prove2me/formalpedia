-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.sinc_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:31:04.660008+00:00
-- url     : https://prove2.me/submissions/668c6399-a308-4caa-8d46-73ed7bb9932a

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.sinc_neg
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (u : ℝ) : sinc (-u) = sinc u := by

  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · rw [sinc, sinc, if_neg (by simpa using hu), if_neg hu, mul_neg, Real.sin_neg]
    field_simp

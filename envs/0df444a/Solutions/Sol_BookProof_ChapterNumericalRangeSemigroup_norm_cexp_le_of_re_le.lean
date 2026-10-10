-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:26.29115+00:00
-- url     : https://prove2.me/submissions/886f8487-f7c5-4946-b77c-aa66a0cfce35

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {ω t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z.re ≤ ω) :
    ‖Complex.exp ((t : ℂ) * z)‖ ≤ Real.exp (ω * t) := by

  rw [Complex.norm_exp]
  have : ((t : ℂ) * z).re = t * z.re := by simp
  rw [this]
  exact Real.exp_le_exp.mpr (by nlinarith)

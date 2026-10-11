-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_eq_zero_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:28.758196+00:00
-- url     : https://prove2.me/submissions/2421e005-5416-40a8-a334-6f3874e8254a

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.radialBump_eq_zero_of_one_le
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {z : ℂ} (h : 1 ≤ ‖z‖) : radialBump z = 0 := by

  refine expNegInvGlue.zero_of_nonpos ?_
  have : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  simp only [Complex.normSq_eq_norm_sq]
  linarith

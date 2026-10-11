-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_pos_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:30.297032+00:00
-- url     : https://prove2.me/submissions/5d2ad693-5595-45b2-8d12-a6f97d5ef59c

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.radialBump_pos_of_lt_one
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {z : ℂ} (h : ‖z‖ < 1) : 0 < radialBump z := by

  refine expNegInvGlue.pos_of_pos ?_
  have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  simp only [Complex.normSq_eq_norm_sq]
  linarith

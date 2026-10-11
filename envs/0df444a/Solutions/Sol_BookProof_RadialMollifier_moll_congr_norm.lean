-- Prove2me | solution 1 for BookProof.RadialMollifier.moll_congr_norm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:38.114107+00:00
-- url     : https://prove2.me/submissions/dc30c559-61f8-436b-8c58-cf1d289729e3

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.moll_congr_norm
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_radialBump_congr_norm
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {δ : ℝ} {z w : ℂ} (h : ‖z‖ = ‖w‖) : moll δ z = moll δ w := by

  simp only [moll]
  congr 1
  refine radialBump_congr_norm ?_
  simp [h]

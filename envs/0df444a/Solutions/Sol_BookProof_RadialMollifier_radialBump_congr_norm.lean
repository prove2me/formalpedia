-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_congr_norm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:27.508306+00:00
-- url     : https://prove2.me/submissions/22f26986-8833-4ec2-b928-95c09f04b989

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.radialBump_congr_norm
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {z w : ℂ} (h : ‖z‖ = ‖w‖) :
    radialBump z = radialBump w := by

  simp only [radialBump, Complex.normSq_eq_norm_sq, h]

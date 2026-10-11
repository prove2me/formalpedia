-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:33.161105+00:00
-- url     : https://prove2.me/submissions/0e425e98-49e4-4af6-8e78-2e50c61e4cbe

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.radialBump_hasCompactSupport
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_radialBump_support
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : HasCompactSupport radialBump := by

  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 1)
  rw [radialBump_support]
  exact ball_subset_closedBall

-- Prove2me | solution 1 for BookProof.RadialMollifier.moll_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:41.782177+00:00
-- url     : https://prove2.me/submissions/cd9af5de-c48b-4396-9ff4-75a1a4d94a6a

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.moll_hasCompactSupport
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_moll_support_subset
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (moll δ) := by

  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) δ)
  exact (moll_support_subset hδ).trans ball_subset_closedBall

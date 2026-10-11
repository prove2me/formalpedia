-- Prove2me | solution 1 for BookProof.RadialMollifier.moll_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:40.566192+00:00
-- url     : https://prove2.me/submissions/2ba96746-e6b0-4cd0-b8f5-fc44b23056cd

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.moll_support_subset
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_moll_eq_zero_of_le
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {δ : ℝ} (hδ : 0 < δ) :
    Function.support (moll δ) ⊆ ball (0 : ℂ) δ := by

  intro z hz
  simp only [Function.mem_support] at hz
  simp only [mem_ball, dist_zero_right]
  by_contra hcon
  exact hz (moll_eq_zero_of_le hδ (not_lt.1 hcon))

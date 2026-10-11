-- Prove2me | solution 1 for BookProof.RadialMollifier.moll_continuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:36.87712+00:00
-- url     : https://prove2.me/submissions/f99a728a-dd59-401e-a416-27fe44967794

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.moll_continuous
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_moll_contDiff
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (δ : ℝ) : Continuous (moll δ) := (moll_contDiff δ).continuous

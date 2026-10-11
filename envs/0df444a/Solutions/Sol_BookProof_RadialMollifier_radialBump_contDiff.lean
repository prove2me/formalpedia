-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:25.022899+00:00
-- url     : https://prove2.me/submissions/ba4a4410-95ad-40e7-a78b-f65250b0faad

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.radialBump_contDiff
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_contDiff_normSq
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : ContDiff ℝ ∞ radialBump := expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_normSq)

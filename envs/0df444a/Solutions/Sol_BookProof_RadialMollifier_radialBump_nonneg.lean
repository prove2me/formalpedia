-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:02:07.90891+00:00
-- url     : https://prove2.me/submissions/7b2562e7-61a2-4ec1-9264-d7e0103b202c

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.radialBump_nonneg
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section
open BookProof.RadialMollifier

theorem solution(z : ℂ) : 0 ≤ radialBump z := by
  unfold radialBump
  exact expNegInvGlue.nonneg _

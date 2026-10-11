-- Prove2me | solution 1 for BookProof.RadialMollifier.moll_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:56:41.211102+00:00
-- url     : https://prove2.me/submissions/ae97a495-ee54-4eb0-9e6f-2eb3ed841792

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_nonneg
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section
open BookProof.RadialMollifier

theorem solution(δ : ℝ) (z : ℂ) : 0 ≤ moll δ z := by
  unfold moll radialMass
  exact div_nonneg (expNegInvGlue.nonneg _)
    (mul_nonneg (MeasureTheory.integral_nonneg fun z => expNegInvGlue.nonneg _) (sq_nonneg _))

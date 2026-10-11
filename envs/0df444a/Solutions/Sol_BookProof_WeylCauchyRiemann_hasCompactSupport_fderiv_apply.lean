-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.hasCompactSupport_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:58.683201+00:00
-- url     : https://prove2.me/submissions/2150c6da-3eb3-4a83-9b2b-1aaae05db05c

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.hasCompactSupport_fderiv_apply
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (v : ℂ) :
    HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z v) := by

  refine HasCompactSupport.of_support_subset_isCompact hψc.isCompact ?_
  intro z hz
  have : fderiv ℝ ψ z ≠ 0 := by
    intro h
    apply hz
    simp [h]
  exact support_fderiv_subset ℝ (f := ψ) this

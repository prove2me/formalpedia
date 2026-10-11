-- Prove2me | solution 1 for BookProof.RadialMollifier.moll_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:35.540682+00:00
-- url     : https://prove2.me/submissions/3b57606d-6bf6-4a1d-a79b-a7a24713d49d

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.moll_contDiff
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_radialBump_contDiff
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (δ : ℝ) : ContDiff ℝ ∞ (moll δ) := by

  have h : ContDiff ℝ ∞ (fun z : ℂ => radialBump (δ⁻¹ • z)) :=
    radialBump_contDiff.comp (contDiff_const_smul _)
  exact h.div_const _

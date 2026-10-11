-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.mollify_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:36.549484+00:00
-- url     : https://prove2.me/submissions/68450032-a555-490f-b51a-fd7187352ed1

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.mollify_contDiff
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_eq_convolution_right
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {F : ℂ → ℂ} (hF : LocallyIntegrable F) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ContDiff ℝ ∞ (mollify F χ) := by

  rw [mollify_eq_convolution_right]
  exact hχc.contDiff_convolution_right _ hF hχ

-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.mollify_eq_convolution_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:35.004837+00:00
-- url     : https://prove2.me/submissions/46858ee0-cd1b-46bd-921d-04bf66500f50

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.mollify_eq_convolution_right
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_eq_convolution_left
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (F : ℂ → ℂ) (χ : ℂ → ℝ) :
    mollify F χ = F ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] χ := by

  rw [mollify_eq_convolution_left, convolution_flip]

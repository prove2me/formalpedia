-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.mollify_eq_convolution_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:33.486505+00:00
-- url     : https://prove2.me/submissions/673e0814-6469-451c-9b8c-2b45add9423f

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.mollify_eq_convolution_left
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (F : ℂ → ℂ) (χ : ℂ → ℝ) :
    mollify F χ = χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F := by

  funext z
  rw [convolution_eq_swap]
  simp [mollify, Complex.real_smul]

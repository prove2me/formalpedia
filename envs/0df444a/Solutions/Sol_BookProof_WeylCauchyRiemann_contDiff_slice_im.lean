-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.contDiff_slice_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:20.907285+00:00
-- url     : https://prove2.me/submissions/3ecf3d6b-380f-4bb3-8519-6ee97bc20997

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.contDiff_slice_im
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (x : ℝ) : ContDiff ℝ ∞ (fun t : ℝ => (x : ℂ) + t * Complex.I) := by

  exact contDiff_const.add ((Complex.ofRealCLM.contDiff).mul contDiff_const)

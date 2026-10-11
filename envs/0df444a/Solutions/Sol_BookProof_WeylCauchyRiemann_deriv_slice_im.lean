-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.deriv_slice_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:57.785512+00:00
-- url     : https://prove2.me/submissions/6c086b6e-7152-4c9a-8984-7554ae54ac70

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.deriv_slice_im
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x y : ℝ) :
    deriv (fun t : ℝ => ψ ((x : ℂ) + t * Complex.I)) y
      = fderiv ℝ ψ ((x : ℂ) + y * Complex.I) Complex.I := by

  have hg : HasDerivAt (fun t : ℝ => (x : ℂ) + t * Complex.I) Complex.I y := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add
      ((x : ℂ))
  have := (hψ ((x : ℂ) + y * Complex.I)).hasFDerivAt.comp_hasDerivAt y hg
  exact this.deriv

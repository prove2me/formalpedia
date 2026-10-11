-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.deriv_slice_re
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:56.834846+00:00
-- url     : https://prove2.me/submissions/da649094-bdca-41d3-b256-d0afeeec652d

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.deriv_slice_re
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x y : ℝ) :
    deriv (fun t : ℝ => ψ ((t : ℂ) + y * Complex.I)) x
      = fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1 := by

  have hg : HasDerivAt (fun t : ℝ => (t : ℂ) + y * Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
  have := (hψ ((x : ℂ) + y * Complex.I)).hasFDerivAt.comp_hasDerivAt x hg
  exact this.deriv

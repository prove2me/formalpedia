-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:45:23.036564+00:00
-- url     : https://prove2.me/submissions/d7b437fa-2500-41d8-a3f4-4c8238ae96c8

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [m.IsAddHaarMeasure]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
omit [m.IsAddHaarMeasure] in
/-- The gradient of a compactly supported `C²` function is integrable for every exponential tilt of
`m.tilted (-V)`. -/
theorem solution {V f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (z : E) : Integrable (gradient f) (FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) := by
    have hfd : Continuous (fderiv ℝ f) :=
      hf.continuous_fderiv (by norm_num)
    have hgrad : Continuous (gradient f) := by
      change Continuous
        (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
      exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp hfd
    have hfd_cs : HasCompactSupport (fderiv ℝ f) :=
      hfc.fderiv (𝕜 := ℝ)
    have hgrad_cs : HasCompactSupport (gradient f) := by
      change HasCompactSupport
        (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
      exact hfd_cs.comp_left (InnerProductSpace.toDual ℝ E).symm.map_zero
    unfold FunctionalInequalities.Analysis.BakryEmery.expTilt
    exact hgrad.integrable_of_hasCompactSupport hgrad_cs

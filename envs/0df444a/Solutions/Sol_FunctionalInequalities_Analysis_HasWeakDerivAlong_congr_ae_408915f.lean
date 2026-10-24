-- Prove2me | solution 1 for FunctionalInequalities.Analysis.HasWeakDerivAlong.congr_ae_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:53:48.473427+00:00
-- url     : https://prove2.me/submissions/28b30df2-1259-4aaf-b538-6e768a6caadb

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis.HasWeakDerivAlong
end FunctionalInequalities.Analysis.HasWeakDerivAlong
open FunctionalInequalities.Analysis.HasWeakDerivAlong in
/-- Weak directional derivatives are invariant under almost-everywhere
changes of both the function and its derivative. Local integrability is produced. -/
theorem solution {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {f f' g g' : E → ℝ} {v : E}
    (h : FunctionalInequalities.Analysis.HasWeakDerivAlong f g v)
    (hf : f =ᵐ[(volume : Measure E)] f')
    (hg : g =ᵐ[(volume : Measure E)] g') :
    FunctionalInequalities.Analysis.HasWeakDerivAlong f' g' v := by
  refine ⟨h.1.congr hf, h.2.1.congr hg, ?_⟩
  intro ψ hψ hψc
  have ef :
      (∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, f' x * fderiv ℝ ψ x v ∂(volume : Measure E) := by
    apply integral_congr_ae
    exact hf.mono (fun x hx => congrArg (fun r : ℝ => r * fderiv ℝ ψ x v) hx)
  have eg :
      (∫ x, g x * ψ x ∂(volume : Measure E)) =
        ∫ x, g' x * ψ x ∂(volume : Measure E) := by
    apply integral_congr_ae
    exact hg.mono (fun x hx => congrArg (fun r : ℝ => r * ψ x) hx)
  calc
    (∫ x, f' x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) := ef.symm
    _ = -∫ x, g x * ψ x ∂(volume : Measure E) := h.2.2 ψ hψ hψc
    _ = -∫ x, g' x * ψ x ∂(volume : Measure E) :=
      congrArg (fun r : ℝ => -r) eg

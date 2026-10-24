-- Prove2me | solution 1 for FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:55:27.052781+00:00
-- url     : https://prove2.me/submissions/d6f6dc64-8f61-486b-8877-e49da550b624

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
section LW3B1WeakDerivativeMollification
open MeasureTheory Set Filter
open scoped Topology Convolution
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Mollification commutes with weak derivatives** (weak Letwin route, generic): if `g` is the weak derivative
of `f` along `v`, then `φ.normed ⋆ f` is smooth with `∂ᵥ(φ.normed ⋆ f) = φ.normed ⋆ g`. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f g : E → ℝ} {v : E} (h : FunctionalInequalities.Analysis.HasWeakDerivAlong f g v) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
      convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  let ρ : E → ℝ := φ.normed volume
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hρ : ContDiff ℝ 1 ρ := φ.contDiff_normed (n := 1)
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  let ψ : E → ℝ := fun y => ρ (x - y)
  have hψ : ContDiff ℝ 1 ψ :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hψd (y : E) :
      fderiv ℝ ψ y v = -(fderiv ℝ ρ (x - y) v) := by
    have hd := ((hρ.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
    have he := congrArg (fun A : E →L[ℝ] ℝ => A v) hd.fderiv
    simpa only [ψ, Function.comp_def, ContinuousLinearMap.comp_apply,
      neg_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.map_neg] using he
  have hw := h.2.2 ψ hψ hψc
  simp_rw [hψd, mul_neg] at hw
  rw [integral_neg] at hw
  have hi :
      (∫ y, f y * fderiv ℝ ρ (x - y) v ∂(volume : Measure E)) =
        ∫ y, g y * ρ (x - y) ∂(volume : Measure E) :=
    neg_injective hw
  have hint :
      Integrable
        (fun y => (ContinuousLinearMap.precompL E L)
          (fderiv ℝ ρ (x - y)) (f y))
        (volume : Measure E) :=
    ((hρc.fderiv ℝ).convolutionExists_left
      (ContinuousLinearMap.precompL E L)
      (hρ.continuous_fderiv one_ne_zero) h.1 x).integrable_swap
  have hconv :
      fderiv ℝ (convolution ρ f L volume) x v =
        ∫ y, fderiv ℝ ρ (x - y) v * f y ∂(volume : Measure E) := by
    rw [(hρc.hasFDerivAt_convolution_left L hρ h.1 x).fderiv]
    rw [convolution_eq_swap (ContinuousLinearMap.precompL E L)]
    rw [ContinuousLinearMap.integral_apply hint]
    rfl
  change fderiv ℝ (convolution ρ f L volume) x v =
    convolution ρ g L volume x
  calc
    fderiv ℝ (convolution ρ f L volume) x v =
        ∫ y, fderiv ℝ ρ (x - y) v * f y ∂(volume : Measure E) := hconv
    _ = ∫ y, f y * fderiv ℝ ρ (x - y) v ∂(volume : Measure E) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => mul_comm _ _
    _ = ∫ y, g y * ρ (x - y) ∂(volume : Measure E) := hi
    _ = convolution ρ g L volume x := by
      rw [convolution_eq_swap L]
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      change g y * ρ (x - y) = ρ (x - y) * g y
      exact mul_comm _ _

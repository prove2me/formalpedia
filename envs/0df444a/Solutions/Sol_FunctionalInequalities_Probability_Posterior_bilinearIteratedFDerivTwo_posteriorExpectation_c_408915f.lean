-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:06:51.760994+00:00
-- url     : https://prove2.me/submissions/a78a94b2-5f01-4e17-96b2-07301e71c88a

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorExpectation_c_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_covariance_hasDerivAt_of_compact_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_fderiv_posteriorExpectation_c_apply_408915f

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Probability.Posterior.line_hasDerivAt (c h : E) : HasDerivAt (fun t : ℝ => c + t • h) h 0 := by
  convert! ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add c using 1
  simp only [one_smul]
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- The `c`-Hessian of the posterior expectation: `Cov(f, ⟪h,x⟫⟪k,x⟫) − (∫⟪h,x⟫) Cov(f,⟪k,x⟫) − (∫⟪k,x⟫) Cov(f,⟪h,x⟫)`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (h k : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ y Q f) c h k =
      covariance f (fun x => ⟪h, x⟫ * ⟪k, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) -
        (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) *
          covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) -
        (∫ x, ⟪k, x⟫ ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) *
          covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) := by
  have hsm := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c_408915f μ hc hf hC hfb Q
  have hsm2 : ContDiff ℝ 2 (fun y => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ y Q f) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hsm2]
  have hD := (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hsm2 k c).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (line_hasDerivAt c h) (by simp)
  have hφ : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q) := by unfold FunctionalInequalities.Probability.Posterior.quadraticExponent; fun_prop
  have hh : Continuous (fun x : E => ⟪h, x⟫) := by fun_prop
  have hk : Continuous (fun x : E => ⟪k, x⟫) := by fun_prop
  have hN := FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact_408915f μ hc hφ hh hk hf hC hfb
  have hphase (t : ℝ) : FunctionalInequalities.Probability.Posterior.quadraticExponent (c + t • h) Q =
      fun x => FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x + t * ⟪h, x⟫ := by
    funext x
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, inner_add_left, real_inner_smul_left]
    ring
  have hfun : (fun y => fderiv ℝ (fun z => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ z Q f) y k) =
      fun y => covariance f (fun x => ⟪k, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q)) := by
    funext y
    exact FunctionalInequalities.Probability.Posterior.fderiv_posteriorExpectation_c_apply_408915f μ hc hf hC hfb y Q k
  have hD' := hD
  simp only [Function.comp_def, hfun, hphase] at hD'
  simpa only [hfun] using hD'.unique hN

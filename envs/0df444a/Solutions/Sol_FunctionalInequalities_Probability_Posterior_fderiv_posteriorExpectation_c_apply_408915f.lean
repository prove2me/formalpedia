-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.fderiv_posteriorExpectation_c_apply_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:05:32.898978+00:00
-- url     : https://prove2.me/submissions/d4ad4e67-cb1b-45b8-91b4-13678a28dd81

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
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_expectation_hasDerivAt_of_compact_408915f

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The exponent is affine along a parameter line: `E_{c+th, Q+tH} = E_{c,Q} + t E_{h,H}`. -/
theorem FunctionalInequalities.Probability.Posterior.quadraticExponent_add_smul (c h : E) (Q H : E →L[ℝ] E) (t : ℝ) (x : E) :
    quadraticExponent (c + t • h) (Q + t • H) x = quadraticExponent c Q x + t * quadraticExponent h H x := by
  simp only [quadraticExponent, inner_add_left, real_inner_smul_left, add_apply, smul_apply]
  ring
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- **Parameter response of the posterior of a compactly supported prior**: for every `(c, Q)` (including
`c = Q = 0`) and measurable `f` bounded on the support, `t ↦ ∫ f d(μ.tilted E_{c+th,Q+tH})` has derivative
`Cov_{μ.tilted E_{c,Q}}(f, E_{h,H})` at `t = 0`. -/
theorem FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c h : E) (Q H : E →L[ℝ] E)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, f x
      ∂((μ : Measure E).tilted (quadraticExponent (c + t • h) (Q + t • H))))
      (covariance f (quadraticExponent h H) ((μ : Measure E).tilted (quadraticExponent c Q))) 0 := by
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  have hg : Continuous (quadraticExponent h H) := by unfold quadraticExponent; fun_prop
  have hphase (t : ℝ) : quadraticExponent (c + t • h) (Q + t • H) =
      fun x => quadraticExponent c Q x + t * quadraticExponent h H x := by
    funext x
    exact quadraticExponent_add_smul c h Q H t x
  simpa only [hphase] using
    expectation_hasDerivAt_of_compact_408915f μ hc hφ hg hf hC hb
end
end
end
end
end

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
/-- The `c`-gradient of the posterior expectation is the covariance with the linear score. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (h : E) :
    fderiv ℝ (fun y => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ y Q f) c h =
      covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) := by
  have hsm := FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c_408915f μ hc hf hC hfb Q
  have hsm2 : ContDiff ℝ 2 (fun y => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ y Q f) :=
    hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hD := (hsm2.differentiable (by norm_num) c).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (line_hasDerivAt c h) (by simp)
  have hN := FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_quadraticExponent_of_compact μ hc c h Q 0 hf hC hfb
  have hg : FunctionalInequalities.Probability.Posterior.quadraticExponent h (0 : E →L[ℝ] E) = fun x => ⟪h, x⟫ := by
    funext x
    simp [FunctionalInequalities.Probability.Posterior.quadraticExponent]
  have hN' : HasDerivAt (fun t : ℝ => FunctionalInequalities.Probability.Posterior.posteriorExpectation μ (c + t • h) Q f)
      (covariance f (fun x => ⟪h, x⟫) ((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q))) 0 := by
    simpa only [FunctionalInequalities.Probability.Posterior.posteriorExpectation, smul_zero, add_zero, hg] using hN
  exact hD.unique hN'

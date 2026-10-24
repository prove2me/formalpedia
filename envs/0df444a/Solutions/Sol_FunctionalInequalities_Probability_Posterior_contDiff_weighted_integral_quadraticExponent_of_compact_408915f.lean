-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:57:41.975048+00:00
-- url     : https://prove2.me/submissions/129737cc-b56e-49e5-b5eb-a89a6e854801

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
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_integrable_exp_norm_mul_of_compact_408915f

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
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
/-- The unnormalized integral `c ↦ ∫ e^{E_{c,Q}} f dμ` is `C^∞` under a compact prior (weighted-integral
smoothness inside every exponential radius). -/
theorem solution (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (Q : E →L[ℝ] E) :
    ContDiff ℝ ∞ (fun c : E => ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * f x ∂(μ : Measure E)) := by
  let g : E → ℝ := fun x => Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x) * f x
  have hp : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent (0 : E) Q) := by unfold FunctionalInequalities.Probability.Posterior.quadraticExponent; fun_prop
  have hg : AEStronglyMeasurable g (μ : Measure E) := (Real.continuous_exp.comp hp).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hi (s : ℝ) : Integrable (fun x => Real.exp (s * ‖x‖) * ‖g x‖) (μ : Measure E) :=
    FunctionalInequalities.Probability.Posterior.integrable_exp_norm_mul_of_compact_408915f μ hc hf hC hfb Q s
  have hs : ContDiff ℝ ∞ (fun c : E => ∫ x, Real.exp ⟪c, x⟫ • g x ∂(μ : Measure E)) := by
    rw [contDiff_iff_contDiffAt]
    intro c
    have hon := FunctionalInequalities.Analysis.BakryEmery.weighted_integral_contDiffOn (μ : Measure E) hg
      (r := ‖c‖ + 1) (fun s _hs => hi s)
    apply hon.contDiffAt
    exact Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using (lt_add_one ‖c‖))
  have heq : (fun c : E => ∫ x, Real.exp ⟪c, x⟫ • g x ∂(μ : Measure E)) =
      fun c => ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * f x ∂(μ : Measure E) := by
    funext c
    congr 1
    funext x
    dsimp [g]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, inner_zero_left, zero_sub]
    ring
  rw [heq] at hs
  exact hs

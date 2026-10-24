-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.integrable_exp_norm_mul_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:56:30.872993+00:00
-- url     : https://prove2.me/submissions/6be7d058-acc0-465c-98a5-83ed9fb17aaf

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
/-- Under a compact prior, `e^{s‖x‖} ‖e^{E_{0,Q}} f‖` is integrable for every `s` (bounded `f` on the support). -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (_hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (Q : E →L[ℝ] E) (s : ℝ) :
    Integrable (fun x => Real.exp (s * ‖x‖) * ‖Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x) * f x‖) (μ : Measure E) := by
  have hφ : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent (0 : E) Q) := by unfold FunctionalInequalities.Probability.Posterior.quadraticExponent; fun_prop
  obtain ⟨P, _hP, hp⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc hφ
  obtain ⟨R, _hR, hR⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc
    (continuous_norm : Continuous (fun x : E => ‖x‖))
  have hmeas : Measurable (fun x => Real.exp (s * ‖x‖) * ‖Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x) * f x‖) :=
    ((Real.continuous_exp.comp (continuous_norm.const_mul s)).measurable).mul (((Real.continuous_exp.comp hφ).measurable.mul hf).norm)
  apply FunctionalInequalities.Probability.Posterior.integrable_of_bound_on_support μ hmeas (Real.exp (|s| * R + P) * C)
  intro x hx
  have hnorm : ‖x‖ ≤ R := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using hR x hx
  have hleft : s * ‖x‖ ≤ |s| * R :=
    (mul_le_mul_of_nonneg_right (le_abs_self s) (norm_nonneg x)).trans
      (mul_le_mul_of_nonneg_left hnorm (abs_nonneg s))
  have hright : FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x ≤ P :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hp x hx)
  change ‖Real.exp (s * ‖x‖) * ‖Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent 0 Q x) * f x‖‖ ≤ Real.exp (|s| * R + P) * C
  rw [norm_mul, norm_norm, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
  exact mul_le_mul (Real.exp_le_exp.mpr (add_le_add hleft hright)) (hfb x hx)
    (norm_nonneg _) (Real.exp_nonneg _)

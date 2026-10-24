-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.norm_toLp_smul_gradient_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:33:53.530434+00:00
-- url     : https://prove2.me/submissions/92b9c036-7e28-4f1b-a557-31ec5ceda3c9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- Product rule for the gradient. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hg, map_add, map_smulₛₗ, map_smulₛₗ]
  simp
end Gradient
end DifferentialTools
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open Energy Energy.WeightedGradient
section Haar
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **A Caccioppoli-type estimate for the mollified equation.** If a smooth `v` and a continuous
field `H` satisfy the weak equation `∫ Δg v = ∫ ⟪∇g, H⟫ + ∫ g v` for every smooth test `g`
supported in `tsupport χ`, then `‖χ ∇v‖ ≤ 3 ‖v ∇χ‖ + 2 ‖χ H‖` in `L²(m)`. Only the test
`g = χ² v` is used. -/
 theorem solution {χ v : V → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hv : ContDiff ℝ ∞ v) {H : V → V}
    (heq : ∀ g : V → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ tsupport χ →
      ∫ x, Laplacian.laplacian g x * v x ∂m =
        ∫ x, ⟪gradient g x, H x⟫ ∂m + ∫ x, g x * v x ∂m)
    (hA : MemLp (fun x => χ x • gradient v x) 2 m) (hB : MemLp (fun x => v x • gradient χ x) 2 m)
    (hC : MemLp (fun x => χ x • H x) 2 m) :
    ‖hA.toLp _‖ ≤ 3 * ‖hB.toLp _‖ + 2 * ‖hC.toLp _‖ := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  have hχd : Differentiable ℝ χ := hχ1.differentiable one_ne_zero
  have hvd : Differentiable ℝ v := hv1.differentiable one_ne_zero
  -- the test function `g = χ² v`
  set g : V → ℝ := fun x => χ x * χ x * v x with hg_def
  have hg : ContDiff ℝ ∞ g := (hχ.mul hχ).mul hv
  have hgc : HasCompactSupport g := (hχc.mul_right).mul_right
  have hgs : tsupport g ⊆ tsupport χ := by
    refine closure_mono fun x hx => ?_
    simp only [Function.mem_support, hg_def] at hx ⊢
    intro h0
    exact hx (by rw [h0]; ring)
  have hgrad : ∀ x, gradient g x = (χ x * χ x) • gradient v x + (2 * (χ x * v x)) • gradient χ x := by
    intro x
    have h1 : gradient (fun y => χ y * χ y) x = χ x • gradient χ x + χ x • gradient χ x :=
      FunctionalInequalities.Analysis.BakryEmery.gradient_mul (hχd x) (hχd x)
    have h2 := FunctionalInequalities.Analysis.BakryEmery.gradient_mul (f := fun y => χ y * χ y) (g := v) (x := x) ((hχd x).mul (hχd x))
      (hvd x)
    rw [hg_def]
    refine h2.trans ?_
    rw [h1]
    module
  -- integration by parts with the constant weight
  have hibp := FunctionalInequalities.Analysis.BakryEmery.integral_mul_inner_gradient_eq_neg m (w := fun _ => (1 : ℝ)) contDiff_const
    (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgc hv1
  simp only [one_mul, gradient_fun_const, inner_zero_left, add_zero] at hibp
  have heqg := heq g hg hgc hgs
  -- the three `L²` classes and their pairings
  have hAae := hA.coeFn_toLp
  have hBae := hB.coeFn_toLp
  have hCae := hC.coeFn_toLp
  have hint : ∀ (F G : Lp V 2 m) (f g : V → V), (F : V → V) =ᵐ[m] f → (G : V → V) =ᵐ[m] g →
      Integrable (fun x => ⟪f x, g x⟫) m := fun F G f g hF hG =>
    (L2.integrable_inner F G).congr (by filter_upwards [hF, hG] with x e1 e2; rw [e1, e2])
  have hAA : ⟪hA.toLp _, hA.toLp _⟫ = ∫ x, ⟪χ x • gradient v x, χ x • gradient v x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae] with x e; rw [e])
  have hBA : ⟪hB.toLp _, hA.toLp _⟫ = ∫ x, ⟪v x • gradient χ x, χ x • gradient v x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae, hBae] with x e1 e2; rw [e1, e2])
  have hAC : ⟪hA.toLp _, hC.toLp _⟫ = ∫ x, ⟪χ x • gradient v x, χ x • H x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae, hCae] with x e1 e2; rw [e1, e2])
  have hBC : ⟪hB.toLp _, hC.toLp _⟫ = ∫ x, ⟪v x • gradient χ x, χ x • H x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hBae, hCae] with x e1 e2; rw [e1, e2])
  -- `∫ ⟪∇g, ∇v⟫ = ‖A‖² + 2 ⟪B, A⟫`
  have e1 : ∫ x, ⟪gradient g x, gradient v x⟫ ∂m =
      ‖hA.toLp _‖ ^ 2 + 2 * ⟪hB.toLp _, hA.toLp _⟫ := by
    rw [← real_inner_self_eq_norm_sq, hAA, hBA, ← integral_const_mul,
      ← integral_add (hint _ _ _ _ hAae hAae) ((hint _ _ _ _ hBae hAae).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hgrad, inner_add_left, real_inner_smul_left, real_inner_smul_right]
    ring
  -- `∫ ⟪∇g, H⟫ = ⟪A, C⟫ + 2 ⟪B, C⟫`
  have e2 : ∫ x, ⟪gradient g x, H x⟫ ∂m =
      ⟪hA.toLp _, hC.toLp _⟫ + 2 * ⟪hB.toLp _, hC.toLp _⟫ := by
    rw [hAC, hBC, ← integral_const_mul,
      ← integral_add (hint _ _ _ _ hAae hCae) ((hint _ _ _ _ hBae hCae).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hgrad, inner_add_left, real_inner_smul_left, real_inner_smul_right]
    ring
  -- `∫ g v ≥ 0`
  have e3 : 0 ≤ ∫ x, g x * v x ∂m := by
    refine integral_nonneg fun x => ?_
    simp only [hg_def, Pi.zero_apply]
    nlinarith [sq_nonneg (χ x * v x)]
  -- the quadratic inequality
  have hkey : ‖hA.toLp _‖ ^ 2 + 2 * ⟪hB.toLp _, hA.toLp _⟫ +
      (⟪hA.toLp _, hC.toLp _⟫ + 2 * ⟪hB.toLp _, hC.toLp _⟫) ≤ 0 := by
    rw [← e1, ← e2, hibp]
    linarith [heqg, e3]
  have cs1 := abs_real_inner_le_norm (hB.toLp _) (hA.toLp _)
  have cs2 := abs_real_inner_le_norm (hA.toLp _) (hC.toLp _)
  have cs3 := abs_real_inner_le_norm (hB.toLp _) (hC.toLp _)
  have hA0 := norm_nonneg (hA.toLp _)
  have hB0 := norm_nonneg (hB.toLp _)
  have hC0 := norm_nonneg (hC.toLp _)
  have hsq : ‖hA.toLp _‖ ^ 2 ≤ 2 * ‖hB.toLp _‖ * ‖hA.toLp _‖ + ‖hA.toLp _‖ * ‖hC.toLp _‖ +
      2 * ‖hB.toLp _‖ * ‖hC.toLp _‖ := by
    have := neg_abs_le (⟪hB.toLp _, hA.toLp _⟫ : ℝ)
    have := neg_abs_le (⟪hA.toLp _, hC.toLp _⟫ : ℝ)
    have := neg_abs_le (⟪hB.toLp _, hC.toLp _⟫ : ℝ)
    nlinarith
  nlinarith [hsq, hA0, hB0, hC0, mul_nonneg hB0 hC0]

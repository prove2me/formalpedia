-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:54:55.239994+00:00
-- url     : https://prove2.me/submissions/479d6ed7-cd78-4987-a1dc-c90e769a11d9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Dissipation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Dirichlet
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
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
import Mathlib.Analysis.Distribution.TemperateGrowth
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
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cutoff_eq_one_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hasCompactSupport_cutoff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_iteratedFDeriv_cutoff_le_408915f

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

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
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
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) R) := by
    change ContDiff ℝ ∞
      (fun x : E => (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x))
    exact unitBump.contDiff.comp (contDiff_const_smul R⁻¹)
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one (R : ℝ) (x : E) : |cutoff R x| ≤ 1 := by
    change |(unitBump : ContDiffBump (0 : E)) (R⁻¹ • x)| ≤ 1
    have hnonneg :
        0 ≤ (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x) :=
      ContDiffBump.nonneg (unitBump : ContDiffBump (0 : E))
    have hle :
        (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x) ≤ 1 :=
      ContDiffBump.le_one (unitBump : ContDiffBump (0 : E))
    exact abs_le.2 ⟨by linarith, hle⟩
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖∇g(x)‖ = ‖∇¹g(x)‖`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one (g : E → ℝ) (x : E) :
    ‖gradient g x‖ = ‖iteratedFDeriv ℝ 1 g x‖ := by
    rw [gradient, (InnerProductSpace.toDual ℝ E).symm.norm_map,
      norm_iteratedFDeriv_one]
variable (m : Measure E) [m.IsAddHaarMeasure]
end
end
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
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
open Analysis.Semigroup Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
open scoped ContDiff
open Filter Topology Energy Energy.WeightedGradient
section StructuredSpace
variable {F : Type*}
variable [NormedAddCommGroup F]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V]
    [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem FunctionalInequalities.KLS.LogConcave.q_memLp_of_polynomial_bound {g : V → F}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (hg : AEStronglyMeasurable g (ν : Measure V))
    {C : ℝ} {k : ℕ}
    (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    MemLp g 2 (ν : Measure V) := by
  apply (memLp_two_iff_integrable_sq_norm hg).mpr
  apply integrable_of_norm_le_pow_408915f (ν : Measure V) hexp (hg.norm.pow 2)
    (C := C ^ 2) (k := k * 2)
  intro x
  change ‖‖g x‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem FunctionalInequalities.KLS.LogConcave.q_tendsto_toLp [InnerProductSpace ℝ F]
    {a : ℕ → V → F} {b : V → F}
    (ha : ∀ n, MemLp (a n) 2 (ν : Measure V))
    (hb : MemLp b 2 (ν : Measure V))
    {D : V → ℝ} (hD : Integrable D (ν : Measure V))
    (hbound : ∀ n x, ‖a n x - b x‖ ^ 2 ≤ D x)
    (hlocal : ∀ x, ∀ᶠ n : ℕ in atTop, a n x = b x) :
    Tendsto (fun n => (ha n).toLp (a n)) atTop (𝓝 (hb.toLp b)) := by
  have ht : Tendsto (fun n => ∫ x, ‖a n x - b x‖ ^ 2 ∂(ν : Measure V))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_integral_of_dominated_convergence
      (F := fun n x => ‖a n x - b x‖ ^ 2) (f := fun _ => (0 : ℝ)) D
      (fun n => ((ha n).1.sub hb.1).norm.pow 2) hD
      (fun n => ae_of_all _ (fun x => by
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound n x))
      (ae_of_all _ (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hlocal x] with n hn
        simp [hn]))
  have heq (n : ℕ) :
      ‖(ha n).toLp (a n) - hb.toLp b‖ ^ 2 =
        ∫ x, ‖a n x - b x‖ ^ 2 ∂(ν : Measure V) := by
    rw [← real_inner_self_eq_norm_sq, ← (ha n).toLp_sub hb, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((ha n).sub hb).coeFn_toLp] with x hx
    rw [hx, Pi.sub_apply, real_inner_self_eq_norm_sq]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ← heq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hs
private theorem FunctionalInequalities.KLS.LogConcave.q_sq_sub_le {u v : F} {B : ℝ}
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) : ‖u - v‖ ^ 2 ≤ (2 * B) ^ 2 := by
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add hu hv
    _ = 2 * B := by ring
end StructuredSpace
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
include hexp in
/-- A function of temperate growth has its `L²(ν)` class in the domain of the closed unit gradient,
which sends it to the class of `∇f` (only the exponential moments of `ν` are used). -/
theorem solution {f : V → ℝ}
    (hf : f.HasTemperateGrowth) :
    ∃ (hf2 : MemLp f 2 (ν : Measure V)) (hg2 : MemLp (gradient f) 2 (ν : Measure V))
      (hmem : hf2.toLp f ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem⟩ = hg2.toLp (gradient f) := by
  obtain ⟨k, C, hC, hb⟩ := hf.norm_iteratedFDeriv_le_uniform 1
  have hfb (x : V) : ‖f x‖ ≤ C * (1 + ‖x‖) ^ k := by
    simpa only [norm_iteratedFDeriv_zero] using hb 0 (by omega) x
  have hgb (x : V) : ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k := by
    simpa only [FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one] using hb 1 le_rfl x
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf2 := q_memLp_of_polynomial_bound hexp hf.1.continuous.aestronglyMeasurable hfb
  have hg2 := q_memLp_of_polynomial_bound hexp
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hf1).aestronglyMeasurable hgb
  obtain ⟨K₀, hK₀⟩ := FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le_408915f (E := V) 1
  let K : ℝ := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  let A : ℝ := C + C * K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCA : C ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (mul_nonneg hC hK)
  let a : ℕ → V → ℝ := fun n x => FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x * f x
  have ha (n : ℕ) : ContDiff ℝ ∞ (a n) := (FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff _).mul hf.1
  have hac (n : ℕ) : HasCompactSupport (a n) :=
    (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_408915f (by positivity : 0 < (n : ℝ) + 1)).mul_right
  have hab (n : ℕ) (x : V) : ‖a n x‖ ≤ A * (1 + ‖x‖) ^ k := by
    dsimp only [a]
    rw [norm_mul]
    calc
      _ ≤ 1 * (C * (1 + ‖x‖) ^ k) :=
        mul_le_mul (by simpa only [Real.norm_eq_abs] using FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one _ _)
          (hfb x) (norm_nonneg _) zero_le_one
      _ ≤ A * (1 + ‖x‖) ^ k := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right hCA (by positivity)
  have hgab (n : ℕ) (x : V) : ‖gradient (a n) x‖ ≤ A * (1 + ‖x‖) ^ k := by
    have hc1 : ContDiff ℝ 1 (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) : V → ℝ) :=
      (FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff _).of_le (WithTop.coe_le_coe.mpr le_top)
    have hcut : ‖gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ ≤ K := by
      rw [FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one]
      exact (hK₀ _
        (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + 1) x).trans
        (le_max_left _ _)
    dsimp only [a]
    rw [FunctionalInequalities.Analysis.BakryEmery.gradient_mul (hc1.differentiable (by norm_num) x)
      (hf1.differentiable (by norm_num) x)]
    calc
      _ ≤ ‖FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x • gradient f x‖ +
          ‖f x • gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ := norm_add_le _ _
      _ = |FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x| * ‖gradient f x‖ +
          |f x| * ‖gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (C * (1 + ‖x‖) ^ k) + (C * (1 + ‖x‖) ^ k) * K := by
        gcongr
        · exact FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one _ _
        · exact hgb x
        · simpa only [Real.norm_eq_abs] using hfb x
      _ = _ := by dsimp [A]; ring
  have hfA (x : V) : ‖f x‖ ≤ A * (1 + ‖x‖) ^ k :=
    (hfb x).trans (mul_le_mul_of_nonneg_right hCA (by positivity))
  have hgA (x : V) : ‖gradient f x‖ ≤ A * (1 + ‖x‖) ^ k :=
    (hgb x).trans (mul_le_mul_of_nonneg_right hCA (by positivity))
  let D : V → ℝ := fun x => (2 * A) ^ 2 * (1 + ‖x‖) ^ (k * 2)
  have hD : Integrable D (ν : Measure V) := by
    apply FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_408915f _ hexp (by fun_prop)
      (C := (2 * A) ^ 2) (k := k * 2)
    intro x
    exact Real.norm_of_nonneg (by dsimp [D]; positivity) |>.le
  have hlocal (x : V) : ∀ᶠ n : ℕ in atTop, a n =ᶠ[𝓝 x] f := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hx : ‖x‖ < (n : ℝ) + 1 := by linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    dsimp only [a]
    rw [FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one_408915f (by positivity) hy.le, one_mul]
  have hat := q_tendsto_toLp
    (fun n => FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (ha n) (hac n))
    hf2 hD (fun n x => by
      simpa only [D, mul_pow, pow_mul, mul_assoc] using q_sq_sub_le (hab n x) (hfA x))
    (fun x => (hlocal x).mono (fun _ hn => hn.eq_of_nhds))
  have hgat := q_tendsto_toLp
    (fun n => FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport (ha n) (hac n))
    hg2 hD (fun n x => by
      simpa only [D, mul_pow, pow_mul, mul_assoc] using q_sq_sub_le (hgab n x) (hgA x))
    (fun x => (hlocal x).mono (fun _ hn => hn.gradient_eq))
  have hmem (n : ℕ) := hν.toLp_mem_closedWeightedOperator_domain m hi (ha n) (hac n)
  have hgt : Tendsto (fun n =>
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem n⟩)
      atTop (𝓝 (hg2.toLp (gradient f))) := by
    convert hgat using 1
    apply funext
    intro n
    exact hν.closedWeightedOperator_toLp_eq m hi (ha n) (hac n)
  obtain ⟨hmemf, heq⟩ := FunctionalInequalities.Analysis.Semigroup.exists_mem_domain_apply_eq_of_tendsto
    (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi) hmem hat hgt
  exact ⟨hf2, hg2, hmemf, heq⟩

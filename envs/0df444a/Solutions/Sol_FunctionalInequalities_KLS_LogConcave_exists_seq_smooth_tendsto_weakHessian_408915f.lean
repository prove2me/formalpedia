-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_weakHessian_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:50:00.085617+00:00
-- url     : https://prove2.me/submissions/2c5fa487-afb2-48b9-bbb9-0c69ffb0c106

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
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
import Mathlib.Analysis.Calculus.Deriv.Inv
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
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_hessianSq_add_le_of_hasTemperateGrowth_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_tendsto_apply_of_tendsto_adjointComp_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_adjointComp_of_localRegularity_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_408915f

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
section Directional
/-- Difference rule for directional derivatives. -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_sub_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y - g y) x v = fderiv ℝ f x v - fderiv ℝ g x v := by
  rw [fderiv_fun_sub hf hg]
  simp
end Directional
section StdBasis
variable [FiniteDimensional ℝ E]
variable [CompleteSpace E]
/-- `‖∇f‖²` is the sum of the squared directional derivatives in the standard orthonormal basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.norm_gradient_sq_eq_sum (f : E → ℝ) (y : E) :
    ‖gradient f y‖ ^ 2 = ∑ i, fderiv ℝ f y (stdOrthonormalBasis ℝ E i) ^ 2 := by
  rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_left]
  simp only [inner_gradient_left]
end StdBasis
end DifferentialTools
end
end
end
end
end

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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section HessianSq
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_apply (f : E → ℝ) (x : E) :
    hessianSqStdBasis f x = ∑ i, ∑ j,
      (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2 :=
  rfl
end HessianSq
end
end
end
end
end

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end
end
end

section
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff LinearPMap RealInnerProductSpace
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Generator
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
include hνU hU in
/-- **the smooth-test generator identity, value clause**: for `f ∈ C_c^∞(V)`, `T̄†T̄ [f] = [-ℒ f]` with `ℒ f = Δ f - ⟪∇U, ∇f⟫`.
The generator of the heat semigroup `P_t = exp (-t T̄†T̄)` is therefore `ℒ` on smooth compactly
supported tests: `d/dt P_t f |_{t=0} = ℒ f`. -/
theorem FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨(memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f,
          hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ =
      (memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp (fun x => -weightedLaplacian U f x) := by
  rw [adjointComp_apply]
  refine LinearPMap.adjoint_apply_eq
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) _ fun x => ?_
  rw [hν.inner_toLp_neg_weightedLaplacian_eq m hi hνU hU hf hfc x]
  congr 1
  exact (hν.closedWeightedOperator_toLp_eq m hi hf hfc).symm
end Generator
end
end
end
end
end

section
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
section Tilted
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
variable (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
/-- **`C_c^∞(V)` is an operator core of the generator `A = T̄†T̄`.** For `ν = m.tilted (-U)` with
a `C¹` potential and unit weight, every `F ∈ D(A)` is the limit of smooth compactly supported
classes in the graph norm of `A`: there are `fₙ ∈ C_c^∞(V)` with `[fₙ] → F` and `A [fₙ] → A F` in
`L²(ν)`. Equivalently, `ℒ = Δ - ⟪∇U, ∇·⟫` is essentially self-adjoint on `C_c^∞(V)` in `L²(ν)`.

This is the operator-core criterion `exists_seq_smooth_tendsto_adjointComp_of_localRegularity`
with its hypothesis discharged by `toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`; it
is exactly the hypothesis `hcore` of `HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`.
No convexity of `U`, no semigroup and no `Γ₂` input is used. -/
theorem FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (F : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖((adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
          (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
              (ν : Measure V)))‖) atTop (𝓝 0) :=
  hν.exists_seq_smooth_tendsto_adjointComp_of_localRegularity_408915f m hi hνU hU
    (fun u horth _χ hχ hχc =>
      hν.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_408915f m hi hνU hU u horth hχ hχc) F
end Tilted
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
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
section Partial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [CompleteSpace V] [FiniteDimensional ℝ V]
/-- `Σᵢ ‖∇ (∂ᵢ f)(x)‖² = Σᵢ Σⱼ (∇²f(x)(eᵢ, eⱼ))²` in the standard orthonormal basis. -/
private theorem FunctionalInequalities.KLS.LogConcave.sum_norm_gradient_fderiv_apply_sq {f : V → ℝ} (hf : ContDiff ℝ 2 f) (x : V) :
    ∑ i, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2 =
      hessianSqStdBasis f x := by
  rw [hessianSqStdBasis_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_gradient_sq_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hf]
end Partial
/-- A real sequence of nonnegative numbers whose squares tend to zero tends to zero. -/
private theorem FunctionalInequalities.KLS.LogConcave.tendsto_zero_of_sq {α : Type*} {l : Filter α} {u : α → ℝ} (h0 : ∀ a, 0 ≤ u a)
    (h : Tendsto (fun a => u a ^ 2) l (𝓝 0)) : Tendsto u l (𝓝 0) := by
  have h' := (Real.continuous_sqrt.tendsto 0).comp h
  simpa [Function.comp_def, Real.sqrt_sq (h0 _)] using h'
/-- `x ≤ a - ρ b` and `0 ≤ b` give `x ≤ a + |ρ| b`. -/
private theorem FunctionalInequalities.KLS.LogConcave.le_add_abs_mul_of_le_sub {x a b ρ : ℝ} (h : x ≤ a - ρ * b) (hb : 0 ≤ b) :
    x ≤ a + |ρ| * b := by
  nlinarith [neg_abs_le ρ]
section Hessian
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
/-- `T̄ [f]` depends only on the function `f`. -/
private theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_toLp_congr {f g : V → ℝ} (h : f = g)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hg hgc⟩ := by
  subst h; rfl
/-- `T̄ [f - g] = T̄ [f] - T̄ [g]` on smooth compactly supported functions. -/
private theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_toLp_sub {f g : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi (hf.sub hg) (hfc.sub hgc)⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hg hgc⟩ := by
  rw [← LinearPMap.map_sub]
  congr 1
/-- `A [f - g] = A [f] - A [g]` on smooth compactly supported functions. -/
private theorem FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_sub (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {f g : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hf.sub hg) (hfc.sub hgc)⟩ =
      adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ -
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hg hgc⟩ := by
  rw [← LinearPMap.map_sub]
  congr 1
/-- `⟪v, T̄ [f]⟫ = [∂ᵥ f]` for smooth compactly supported `f`. -/
private theorem FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_toLp {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (v : V) :
    (innerSL ℝ v).compLp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩) =
      (memLp_of_contDiff_hasCompactSupport ν (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf v)
        (hfc.fderiv_apply ℝ v)).toLp (fun y => fderiv ℝ f y v) := by
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc]
  refine Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp (innerSL ℝ v)
      ((memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).toLp (gradient f)),
    (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).coeFn_toLp,
    (memLp_of_contDiff_hasCompactSupport ν (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf v)
        (hfc.fderiv_apply ℝ v)).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, h3, innerSL_apply_apply, real_inner_comm, inner_gradient_left]
/-- The smooth curvature inequality in `L²` norms: for `f ∈ C_c^∞` and `∇²U ≥ ρ`,
`Σᵢ ‖T̄ [∂ᵢ f]‖² + ρ ‖T̄ [f]‖² ≤ ‖A [f]‖²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.sum_norm_sq_add_le_of_smooth (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
          (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V i))
          (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩‖ ^ 2 +
      ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 ≤
    ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩‖ ^ 2 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsum : ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
          (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V i))
          (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩‖ ^ 2 =
      ∫ x, hessianSqStdBasis f x ∂(ν : Measure V) := by
    have hmem : ∀ i, MemLp (gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i))) 2
        (ν : Measure V) := fun i =>
      memLp_gradient_of_contDiff_hasCompactSupport
        (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf _) (hfc.fderiv_apply ℝ _)
    calc _ = ∑ i, ∫ x, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2
          ∂(ν : Measure V) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hν.closedWeightedOperator_toLp_eq m hi (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf _)
            (hfc.fderiv_apply ℝ _), L2.norm_toLp_sq]
      _ = ∫ x, ∑ i, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2
          ∂(ν : Measure V) :=
          (integral_finsetSum _ fun i _ =>
            (memLp_two_iff_integrable_sq_norm (hmem i).1).1 (hmem i)).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun x =>
          sum_norm_gradient_fderiv_apply_sq hf2 x)
  rw [hsum, hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    hν.adjointComp_toLp_eq m hi hνU hU hf hfc, L2.norm_toLp_sq, L2.norm_toLp_sq]
  simp only [norm_neg, Real.norm_eq_abs, sq_abs]
  have hexp' : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-U)) :=
    hνU ▸ hexp
  rw [hνU]
  have h := integral_hessianSq_add_le_of_hasTemperateGrowth_408915f m hUt hexp'
    (hfc.hasTemperateGrowth hf) hH
  simpa only [Real.norm_eq_abs, sq_abs] using h
/-- The smooth curvature inequality on differences, for one direction `i`:
`‖T̄ [∂ᵢ f] - T̄ [∂ᵢ g]‖² ≤ ‖A [f] - A [g]‖² - ρ ‖T̄ [f] - T̄ [g]‖²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.norm_sub_sq_le_of_smooth (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f g : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (i : Fin (Module.finrank ℝ V)) :
    ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V i))
            (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hg (stdOrthonormalBasis ℝ V i))
            (hgc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ -
          adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hg hgc⟩‖ ^ 2 -
        ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ -
          hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hg hgc⟩‖ ^ 2 := by
  have hb := sum_norm_sq_add_le_of_smooth m hν hi hνU hUt hU hexp hH (hf.sub hg) (hfc.sub hgc)
  rw [closedWeightedOperator_toLp_sub m hν hi hf hfc hg hgc,
    adjointComp_toLp_sub m hν hi hνU hU hf hfc hg hgc] at hb
  have hpart : ∀ j, hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
          (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty (hf.sub hg) (stdOrthonormalBasis ℝ V j))
          ((hfc.sub hgc).fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V j))
            (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hg (stdOrthonormalBasis ℝ V j))
            (hgc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩ := fun j => by
    have hd1 := FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V j)
    have hd2 := FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hg (stdOrthonormalBasis ℝ V j)
    have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
    have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
    refine (closedWeightedOperator_toLp_congr m hν hi (funext fun y =>
      fderiv_sub_apply (hf1 y) (hg1 y) (stdOrthonormalBasis ℝ V j))
      (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty (hf.sub hg) _) ((hfc.sub hgc).fderiv_apply ℝ _) (hd1.sub hd2)
      ((hfc.fderiv_apply ℝ _).sub (hgc.fderiv_apply ℝ _))).trans ?_
    exact closedWeightedOperator_toLp_sub m hν hi hd1 (hfc.fderiv_apply ℝ _) hd2
      (hgc.fderiv_apply ℝ _)
  rw [Finset.sum_congr rfl fun j _ => by rw [hpart j]] at hb
  have hle := Finset.single_le_sum (f := fun j => ‖hν.closedWeightedOperator m
      (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V j))
            (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hg (stdOrthonormalBasis ℝ V j))
            (hgc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **The approximation behind the weak Hessian estimate.** For `F ∈ D(A)` there are `fₙ ∈ C_c^∞` with
`T̄ [fₙ] → T̄ F`, `A [fₙ] → A F`, and, for every `i`, `⟪eᵢ, T̄ F⟫ ∈ D(T̄)` with
`T̄ [∂ᵢ fₙ] → T̄ ⟪eᵢ, T̄ F⟫`. -/
 theorem solution (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi (hfn n) (hfnc n)⟩) atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) ∧
      Tendsto (fun n => FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩) atTop
        (𝓝 (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) ∧
      ∀ i, ∃ h : (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
        Tendsto (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
              (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty (hfn n) (stdOrthonormalBasis ℝ V i))
              ((hfnc n).fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩) atTop
          (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, h⟩)) := by
  obtain ⟨fn, hfn, hfnc, h1, h2⟩ := hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU F
  have hTF : Tendsto (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi (hfn n) (hfnc n)⟩) atTop
      (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) :=
    FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp_408915f
      (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
      (x := fun n => ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩)
      (tendsto_iff_norm_sub_tendsto_zero.2 h1) (tendsto_iff_norm_sub_tendsto_zero.2 h2)
  have hAF : Tendsto (fun n => FunctionalInequalities.Analysis.Semigroup.adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩) atTop
      (𝓝 (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 h2
  refine ⟨fn, hfn, hfnc, hTF, hAF, fun i => ?_⟩
  have hdf : ∀ n, ContDiff ℝ ∞ (fun y => fderiv ℝ (fn n) y (stdOrthonormalBasis ℝ V i)) :=
    fun n => FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty (hfn n) _
  have hdfc : ∀ n, HasCompactSupport (fun y => fderiv ℝ (fn n) y (stdOrthonormalBasis ℝ V i)) :=
    fun n => (hfnc n).fderiv_apply ℝ _
  have hx : ∀ n, (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hdf n) (hdfc n)).toLp _ ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
    fun n => hν.toLp_mem_closedWeightedOperator_domain m hi (hdf n) (hdfc n)
  have hxa : Tendsto (fun n => (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hdf n) (hdfc n)).toLp _)
      atTop (𝓝 ((innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩))) := by
    have hc := ((((innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLpL 2
      (ν : Measure V))).continuous.tendsto _).comp hTF
    refine hc.congr fun n => ?_
    exact compLp_innerSL_closedWeightedOperator_toLp m hν hi (hfn n) (hfnc n) _
  have hcau : CauchySeq (fun n =>
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hx n⟩) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hA2 := cauchySeq_iff_tendsto_dist_atTop_0.mp hAF.cauchySeq
    have hT2 := cauchySeq_iff_tendsto_dist_atTop_0.mp hTF.cauchySeq
    have hR := (hA2.pow 2).add ((hT2.pow 2).const_mul |ρ|)
    rw [zero_pow two_ne_zero, mul_zero, add_zero] at hR
    refine tendsto_zero_of_sq (fun _ => dist_nonneg)
      (squeeze_zero (fun _ => sq_nonneg _) (fun p => ?_) hR)
    simp only [dist_eq_norm]
    exact le_add_abs_mul_of_le_sub (norm_sub_sq_le_of_smooth m hν hi hνU hUt hU hexp hH
      (hfn p.1) (hfnc p.1) (hfn p.2) (hfnc p.2) i) (sq_nonneg _)
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcau
  obtain ⟨hmem, hTG⟩ := FunctionalInequalities.Analysis.Semigroup.exists_mem_domain_apply_eq_of_tendsto
    (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi) hx hxa hG
  exact ⟨hmem, hTG ▸ hG⟩

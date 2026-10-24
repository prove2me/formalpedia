-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_grad0_iter_sq_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:00:17.690083+00:00
-- url     : https://prove2.me/submissions/b9f00e27-f137-40cb-860b-11a72e06adf6

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiff_tiltAverage_of_memLp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_comp_perm_of_contDiff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_add_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_const_mul_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_le_four_pow_mul_norm_symmetrize_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_normSq_grad0_iter_sub_symField_le_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_norm_symmetrize_taylorField_grad0_iter_sq_le_408915f

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
end
end
end
end
end

section
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
open Filter Topology
universe v
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
section CompleteSpace
variable [CompleteSpace F]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Taylor tensors of a function with smooth tilt average are symmetric multilinear maps. -/
theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_domDomCongr (μ : Measure E) (f : E → F) (hF : ContDiff ℝ ∞ (tiltAverage μ f)) (d : ℕ)
    (σ : Equiv.Perm (Fin d)) : (taylorTensor μ f d).domDomCongr σ = taylorTensor μ f d := by
    ext v
    simp only [taylorTensor, ContinuousMultilinearMap.domDomCongr_apply,
      smul_apply]
    change
      (d.factorial : ℝ)⁻¹ •
          (iteratedFDeriv ℝ d (tiltAverage μ f) 0) (v ∘ σ) =
        (d.factorial : ℝ)⁻¹ •
          (iteratedFDeriv ℝ d (tiltAverage μ f) 0) v
    rw [iteratedFDeriv_comp_perm_of_contDiff_408915f hF d 0 v σ]
end CompleteSpace
end NormedSpace
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
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
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section CompleteSpace
variable [CompleteSpace G]
omit [BorelSpace E] in
/-- Tilt averages only see the `μ`-class of a function: every tilt `μ_z` is absolutely
continuous with respect to `μ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (z : E) :
    tiltAverage μ f z = tiltAverage μ g z := by
  unfold tiltAverage expTilt
  exact integral_congr_ae ((tilted_absolutelyContinuous μ _).ae_le hfg)
omit [BorelSpace E] in
/-- Taylor tensors only see the `μ`-class of a function. -/
theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    taylorTensor μ f d = taylorTensor μ g d := by
  unfold taylorTensor
  rw [show tiltAverage μ f = tiltAverage μ g from funext (tiltAverage_congr_ae μ hfg)]
end CompleteSpace
end NormedSpace
end ScalarLp
end Lp
end
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical
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
section
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `normSq` is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ normSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Tensor
open scoped Classical
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
section
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : ProbabilityMeasure V} {k : ℕ}
/-- `permField` is a left action: `permField (σ * τ) = permField σ ∘ permField τ`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_mul (σ τ : Equiv.Perm (Fin k)) (u : Field ν k) :
    permField (σ * τ) u = permField σ (permField τ u) := rfl
/-- `permField σ` is homogeneous. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_smul (σ : Equiv.Perm (Fin k)) (c : ℝ) (u : Field ν k) :
    permField σ (c • u) = c • permField σ u := rfl
/-- `permField σ` commutes with finite sums. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_sum {ι : Type*} (σ : Equiv.Perm (Fin k)) (s : Finset ι) (f : ι → Field ν k) :
    permField σ (∑ i ∈ s, f i) = ∑ i ∈ s, permField σ (f i) := by
  funext I
  simp [Finset.sum_apply]
end
end
end
end
end
end

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff
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
section
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
section Block
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.one_mem_fixingOutside' (s : Finset Ω) :
    (1 : Equiv.Perm Ω) ∈ fixingOutside s := by
  simp [fixingOutside]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mul_mem_fixingOutside' {s : Finset Ω} {σ τ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) (hτ : τ ∈ fixingOutside s) : σ * τ ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ hτ ⊢
  intro x hx
  simp [Equiv.Perm.coe_mul, hσ x hx, hτ x hx]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_mem_fixingOutside' {s : Finset Ω} {σ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) : σ⁻¹ ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ ⊢
  intro x hx
  have h := congrArg (fun y => σ⁻¹ y) (hσ x hx)
  simpa using h.symm
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_fixingOutside_mul_left {M : Type*} [AddCommMonoid M] {s : Finset Ω}
    {τ : Equiv.Perm Ω} (hτ : τ ∈ fixingOutside s) (g : Equiv.Perm Ω → M) :
    ∑ σ ∈ fixingOutside s, g (τ * σ) = ∑ σ ∈ fixingOutside s, g σ :=
  sum_nbij' (τ * ·) (τ⁻¹ * ·) (fun _ hσ => mul_mem_fixingOutside' hτ hσ)
    (fun _ hσ => mul_mem_fixingOutside' (inv_mem_fixingOutside' hτ) hσ)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => rfl)
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.card_fixingOutside_pos (s : Finset Ω) : (0 : ℝ) < (fixingOutside s).card := by
  exact_mod_cast card_pos.mpr ⟨1, one_mem_fixingOutside' s⟩
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_blockAverage_le (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (v : W) :
    ‖blockAverage ρ s v‖ ≤ ‖v‖ := by
  have hG := card_fixingOutside_pos s
  rw [blockAverage, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hG)]
  calc ((fixingOutside s).card : ℝ)⁻¹ * ‖∑ σ ∈ fixingOutside s, ρ σ v‖
      ≤ ((fixingOutside s).card : ℝ)⁻¹ * ∑ σ ∈ fixingOutside s, ‖ρ σ v‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hG.le)
    _ = ‖v‖ := by
        simp only [LinearIsometryEquiv.norm_map, sum_const, nsmul_eq_mul]
        rw [inv_mul_cancel_left₀ hG.ne']
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.blockAverage_sub (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (v w : W) :
    blockAverage ρ s (v - w) = blockAverage ρ s v - blockAverage ρ s w := by
  simp only [blockAverage, map_sub, sum_sub_distrib, smul_sub]
end Block
section Coordinates
variable {n N : ℕ}
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_le (q : ℕ) (A : Coord n N) : ‖symmetrize n N q A‖ ≤ ‖A‖ :=
  norm_blockAverage_le _ _ _
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_sub (q : ℕ) (A B : Coord n N) :
    symmetrize n N q (A - B) = symmetrize n N q A - symmetrize n N q B :=
  blockAverage_sub _ _ _ _
end Coordinates
section Perm
/-- A permutation of `Fin (a + b)` fixing the first `a` positions permutes the last `b`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_perm_natAdd {a b : ℕ} (σ : Equiv.Perm (Fin (a + b)))
    (hσ : ∀ i : Fin a, σ (Fin.castAdd b i) = Fin.castAdd b i) :
    ∃ π : Equiv.Perm (Fin b), ∀ i, σ (Fin.natAdd a i) = Fin.natAdd a (π i) := by
  have hge : ∀ i : Fin b, a ≤ (σ (Fin.natAdd a i) : ℕ) := by
    intro i
    by_contra hc
    rw [not_le] at hc
    have h1 : σ (Fin.natAdd a i) = σ (Fin.castAdd b ⟨_, hc⟩) := by
      rw [hσ]
      exact Fin.ext rfl
    have h2 := congrArg Fin.val (σ.injective h1)
    simp at h2
    omega
  let g : Fin b → Fin b := fun i =>
    ⟨(σ (Fin.natAdd a i) : ℕ) - a, by have := (σ (Fin.natAdd a i)).isLt; have := i.isLt; omega⟩
  have hg_spec : ∀ i, σ (Fin.natAdd a i) = Fin.natAdd a (g i) := by
    intro i
    apply Fin.ext
    simp only [Fin.val_natAdd, g]
    have := hge i
    omega
  have hg : Function.Injective g := by
    intro i j hij
    have h : σ (Fin.natAdd a i) = σ (Fin.natAdd a j) := by rw [hg_spec, hg_spec, hij]
    have h' := congrArg Fin.val (σ.injective h)
    simp at h'
    exact Fin.ext h'
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), hg_spec⟩
/-- A permutation of `Fin (a + b)` fixing the last `b` positions permutes the first `a`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_perm_castAdd {a b : ℕ} (σ : Equiv.Perm (Fin (a + b)))
    (hσ : ∀ i : Fin b, σ (Fin.natAdd a i) = Fin.natAdd a i) :
    ∃ π : Equiv.Perm (Fin a), ∀ i, σ (Fin.castAdd b i) = Fin.castAdd b (π i) := by
  have hlt : ∀ i : Fin a, (σ (Fin.castAdd b i) : ℕ) < a := by
    intro i
    by_contra hc
    rw [not_lt] at hc
    have hb : (σ (Fin.castAdd b i) : ℕ) - a < b := by
      have := (σ (Fin.castAdd b i)).isLt
      omega
    have h1 : σ (Fin.castAdd b i) = σ (Fin.natAdd a ⟨_, hb⟩) := by
      rw [hσ]
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    have h2 := congrArg Fin.val (σ.injective h1)
    simp at h2
    omega
  let g : Fin a → Fin a := fun i => ⟨σ (Fin.castAdd b i), hlt i⟩
  have hg_spec : ∀ i, σ (Fin.castAdd b i) = Fin.castAdd b (g i) := fun i => Fin.ext rfl
  have hg : Function.Injective g := by
    intro i j hij
    have h : σ (Fin.castAdd b i) = σ (Fin.castAdd b j) := by rw [hg_spec, hg_spec, hij]
    have h' := congrArg Fin.val (σ.injective h)
    simp at h'
    exact Fin.ext h'
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), hg_spec⟩
end Perm
section Taylor
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
include hexp in
/-- `T_d` is additive on `L²(ν)` classes. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_Lp_sub (u v : Lp ℝ 2 (ν : Measure V)) (d : ℕ) :
    taylorTensor (ν : Measure V) (⇑(u - v)) d =
      taylorTensor (ν : Measure V) (⇑u) d - taylorTensor (ν : Measure V) (⇑v) d := by
  have h1 : (⇑(u - v)) =ᵐ[(ν : Measure V)] fun x => u x + (-1 : ℝ) * v x := by
    filter_upwards [Lp.coeFn_sub u v] with x hx
    rw [hx, Pi.sub_apply]
    ring
  rw [taylorTensor_congr_ae _ h1 d,
    taylorTensor_add_408915f _ hexp (Lp.memLp u) ((Lp.memLp v).const_mul (-1)) d,
    taylorTensor_const_mul_408915f, neg_one_smul, sub_eq_add_neg]
include hexp in
/-- `taylorField d` is additive. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField_sub (d : ℕ) {k : ℕ} (u v : Field ν k) :
    taylorField d (u - v) = taylorField d u - taylorField d v := by
  ext J
  simp only [taylorField, PiLp.toLp_apply, Pi.sub_apply, taylorTensor_Lp_sub hexp,
    PiLp.sub_apply]
  rfl
include hexp in
/-- The Taylor tensors of an `L²` class are symmetric. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_Lp_comp_perm (g : Lp ℝ 2 (ν : Measure V)) {d : ℕ}
    (π : Equiv.Perm (Fin d)) (v : Fin d → V) :
    taylorTensor (ν : Measure V) (⇑g) d (v ∘ π) = taylorTensor (ν : Measure V) (⇑g) d v := by
  have h := congrArg (fun Φ => Φ v) (taylorTensor_domDomCongr (ν : Measure V) (⇑g)
    (contDiff_tiltAverage_of_memLp_408915f (ν : Measure V) hexp (Lp.memLp g)) d π)
  simp only [ContinuousMultilinearMap.domDomCongr_apply] at h
  exact h
include hexp in
/-- `taylorField d u` is symmetric in its first `d` (Taylor) index positions. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.slotRep_taylorField_left {d k : ℕ} (u : Field ν k)
    {σ : Equiv.Perm (Fin (d + k))} (hσ : σ ∈ fixingOutside (slots (d + k) 0 d)) :
    slotRep (Module.finrank ℝ V) (d + k) σ (taylorField d u) = taylorField d u := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ
  have hfix : ∀ i : Fin k, σ (Fin.natAdd d i) = Fin.natAdd d i :=
    fun i => hσ _ (by simp [slots])
  obtain ⟨π, hπ⟩ := exists_perm_castAdd σ hfix
  ext J
  change slotPerm _ _ σ (taylorField d u) J = _
  rw [slotPerm_apply]
  simp only [taylorField, PiLp.toLp_apply, Function.comp_apply, hfix, hπ]
  exact taylorTensor_Lp_comp_perm hexp _ π (fun i => stdOrthonormalBasis ℝ V (J (Fin.castAdd k i)))
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `S_q u` is invariant under the permutations of the first `q` positions. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_symField {k q : ℕ} (u : Field ν k) {π : Equiv.Perm (Fin k)}
    (hπ : π ∈ fixingOutside (slots k 0 q)) : permField π (symField q u) = symField q u := by
  rw [symField, permField_smul, permField_sum]
  congr 1
  simp only [← permField_mul]
  exact sum_fixingOutside_mul_left hπ (fun σ => permField σ u)
omit [BorelSpace V] in
/-- `taylorField d u` is symmetric in the `q` positions after the Taylor indices when `u` is
symmetric in its first `q` positions. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.slotRep_taylorField_right {d k q : ℕ} (u : Field ν k)
    (hu : ∀ π ∈ fixingOutside (slots k 0 q), permField π u = u) {σ : Equiv.Perm (Fin (d + k))}
    (hσ : σ ∈ fixingOutside (slots (d + k) d (d + q))) :
    slotRep (Module.finrank ℝ V) (d + k) σ (taylorField d u) = taylorField d u := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ
  have hfix : ∀ i : Fin d, σ (Fin.castAdd k i) = Fin.castAdd k i :=
    fun i => hσ _ (by simp [slots])
  obtain ⟨π, hπ⟩ := exists_perm_natAdd σ hfix
  have hπmem : π ∈ fixingOutside (slots k 0 q) := by
    simp only [fixingOutside, mem_filter, mem_univ, true_and]
    intro i hi
    have h := hσ (Fin.natAdd d i) (by simp [slots] at hi ⊢; omega)
    rw [hπ] at h
    have h' := congrArg Fin.val h
    simp at h'
    exact Fin.ext h'
  ext J
  change slotPerm _ _ σ (taylorField d u) J = _
  rw [slotPerm_apply]
  simp only [taylorField, PiLp.toLp_apply, Function.comp_apply, hfix, hπ]
  have h := congrFun (hu π hπmem) (fun i => J (Fin.natAdd d i))
  rw [permField_apply] at h
  rw [show (fun i => J (Fin.natAdd d (π i))) = (fun i => J (Fin.natAdd d i)) ∘ π from rfl, h]
omit [BorelSpace V] in
/-- **The Taylor bound (29) componentwise**: if `|T_d g| ≤ R^d ‖g‖₂` for every `g ∈ L²(ν)`, then
`|T_d u|² ≤ R^{2d} ‖u‖²` for every tensor field `u`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_sq_le_of_bound {R : ℝ} {d : ℕ}
    (h29 : ∀ g : Lp ℝ 2 (ν : Measure V),
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑g) d)‖ ≤
        R ^ d * ‖g‖) {k : ℕ} (u : Field ν k) :
    ‖taylorField d u‖ ^ 2 ≤ R ^ (2 * d) * normSq u := by
  rw [EuclideanSpace.norm_sq_eq, ← (Fin.appendEquiv d k).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm, normSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun I _ => ?_
  have hI : ∑ J : Fin d → Fin (Module.finrank ℝ V),
      ‖taylorField d u (Fin.appendEquiv d k (J, I))‖ ^ 2 =
        ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑(u I)) d)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp [taylorField, coordTensor_apply, Fin.append_left, Fin.append_right]
  rw [hI, pow_mul', ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h29 (u I)) 2
end Taylor
section Constants
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.two_le_two_pow {d : ℕ} (hd : 1 ≤ d) : (2 : ℝ) ≤ 2 ^ d := by
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.const_bound_one {β : ℝ} (hβ : 0 ≤ β) {d : ℕ} (hd : 1 ≤ d) :
    2 * 16 ^ d * β ^ d ≤ (2 ^ 20 * max 1 β ^ 2) ^ d := by
  have hM : β ≤ max 1 β ^ 2 := by
    have h1 : (1 : ℝ) ≤ max 1 β := le_max_left _ _
    nlinarith [le_max_right 1 β]
  have h16 : 2 * (16 : ℝ) ^ d ≤ (2 ^ 20) ^ d :=
    calc 2 * (16 : ℝ) ^ d ≤ 2 ^ d * 16 ^ d :=
          mul_le_mul_of_nonneg_right (two_le_two_pow hd) (by positivity)
      _ = 32 ^ d := by rw [← mul_pow]; norm_num
      _ ≤ (2 ^ 20) ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  rw [mul_pow]
  exact mul_le_mul h16 (pow_le_pow_left₀ hβ hM d) (by positivity) (by positivity)
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.const_bound_two (β : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    2 * (1 + 4 ^ d) ^ 2 * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * max 1 β ^ (2 * d)) ≤
      (2 ^ 20 * max 1 β ^ 2) ^ d := by
  have h4 : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  have h44 : ((4 : ℝ) ^ d) ^ 2 = 16 ^ d := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hA : (1 + (4 : ℝ) ^ d) ^ 2 ≤ 4 * 16 ^ d := by nlinarith
  have hdle : (d : ℝ) ≤ 2 ^ d := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hB : ((2 * d : ℕ) : ℝ) ^ 4 ≤ 16 * 16 ^ d := by
    push_cast
    have : (d : ℝ) ^ 4 ≤ (2 ^ d) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdle 4
    rw [← pow_mul, mul_comm, pow_mul] at this
    norm_num at this
    nlinarith
  have hM : max 1 β ^ (2 * d) = (max 1 β ^ 2) ^ d := pow_mul _ _ _
  have hMp : 0 ≤ (max 1 β ^ 2) ^ d := by positivity
  have h512 : (512 : ℝ) ≤ 4096 ^ d :=
    calc (512 : ℝ) ≤ 4096 ^ 1 := by norm_num
      _ ≤ 4096 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have h16 : (0 : ℝ) ≤ 16 ^ d := by positivity
  calc 2 * (1 + 4 ^ d) ^ 2 * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * max 1 β ^ (2 * d))
      ≤ 2 * (4 * 16 ^ d) * (4 * (16 * 16 ^ d) * (max 1 β ^ 2) ^ d) := by
        rw [hM]
        gcongr
    _ = 512 * (16 ^ d * 16 ^ d) * (max 1 β ^ 2) ^ d := by ring
    _ = 512 * 256 ^ d * (max 1 β ^ 2) ^ d := by rw [← mul_pow]; norm_num
    _ ≤ 4096 ^ d * 256 ^ d * (max 1 β ^ 2) ^ d := by gcongr
    _ = (2 ^ 20 * max 1 β ^ 2) ^ d := by rw [← mul_pow, ← mul_pow]; norm_num
end Constants
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
include hνU hUt hexp hC in
/-- **BKL Lemma 3.8** in the route form, with the explicit constant `c = 2^20 max(1, β)²`. Under
the Taylor bound (29), `|T_d g| ≤ R^d ‖g‖₂` for `g ∈ L²(ν)` and `d ≥ 1` (Hilbert–Schmidt norm in
the standard basis), for `f ∈ D(A)`, `d ≥ 1`, `2d ≤ k + 1` and `0 < α_{j+2}² ≤ β/C` for `j < k`:
`|T_d(∇₀h_{k+1})|² ≤ (c/C)^d |T_{2d}(∇₀h_{k+1-d})|² + c^d R^{2d} C Σ_{k+1-2d ≤ j < k} χ_{j+1}`. -/
theorem solution (hCpos : 0 < C) {R : ℝ}
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ V) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain) {β : ℝ} (k d : ℕ)
    (hd : 1 ≤ d) (hdk : 2 * d ≤ k + 1)
    (hα : ∀ j < k, 0 < FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j) ∧ FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j) ^ 2 ≤ β / C) :
    ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k))‖ ^ 2 ≤
      (2 ^ 20 * max 1 β ^ 2 / C) ^ d *
          ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (2 * d) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - d)))‖ ^ 2 +
        (2 ^ 20 * max 1 β ^ 2) ^ d * R ^ (2 * d) * C *
          ∑ j ∈ Finset.Ico (k + 1 - 2 * d) k, FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j) := by
  have hC0 : (0 : ℝ) < C := hCpos
  -- `β ≥ 0` from the first step
  have hβ : 0 ≤ β := by
    obtain ⟨h0, h1⟩ := hα 0 (by omega)
    have : 0 ≤ β / C := (sq_nonneg _).trans h1
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hC0)
  set n := Module.finrank ℝ V
  set u := FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)
  set Y := ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (2 * d) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - d)))‖ ^ 2
  set D := ∑ j ∈ Finset.Ico (k + 1 - 2 * d) k, FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j)
  set M := max 1 β
  set A : FunctionalInequalities.Analysis.Tensor.Coord n (d + (k + 1)) := FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d u
  set B : FunctionalInequalities.Analysis.Tensor.Coord n (d + (k + 1)) := FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.symField (2 * d) u)
  set SA := FunctionalInequalities.Analysis.Tensor.symmetrize n (d + (k + 1)) (2 * d) A
  -- (56)–(57)
  have hS : ‖SA‖ ^ 2 ≤ (β / C) ^ d * Y := by
    have h := FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_taylorField_grad0_iter_sq_le_408915f m hν hi hνU hUt hexp hC f d d k hd
      (by omega) fun j hj => (hα j hj).2
    rw [show d + d = 2 * d by ring] at h
    exact h
  -- Lemma 2.2 for `T̃ = B`
  have hL22 : ‖B‖ ≤ 4 ^ d * ‖FunctionalInequalities.Analysis.Tensor.symmetrize n (d + (k + 1)) (2 * d) B‖ :=
    FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_symmetrize_408915f (by omega) B
      (fun σ hσ => slotRep_taylorField_left hexp _ hσ)
      (fun σ hσ => slotRep_taylorField_right (q := 2 * d) _
        (fun π hπ => permField_symField _ hπ)
        (by rw [show 3 * d = d + 2 * d by ring] at hσ; exact hσ))
  -- (29) and Lemma 3.3
  have hAB : A - B = FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.symField (2 * d) u) := (taylorField_sub hexp d _ _).symm
  have hS1 := FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_sub_symField_le_408915f m hν hi hνU hUt hexp hC hCpos hf k (2 * d)
    (by omega) hdk fun j _ hj => hα j hj
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg _
  have hR0 : 0 ≤ R ^ (2 * d) := by rw [pow_mul]; positivity
  have hdiff : ‖A - B‖ ^ 2 ≤
      R ^ (2 * d) * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * M ^ (2 * d) * C * D) := by
    rw [hAB]
    exact (norm_taylorField_sq_le_of_bound (fun g => h29 g d hd) _).trans
      (mul_le_mul_of_nonneg_left hS1 hR0)
  -- (59)
  have htri : ‖A‖ ≤ (1 + 4 ^ d) * ‖A - B‖ + 4 ^ d * ‖SA‖ := by
    have h1 : ‖A‖ ≤ ‖A - B‖ + ‖B‖ := by
      calc ‖A‖ = ‖(A - B) + B‖ := by rw [sub_add_cancel]
        _ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
    have h2 : ‖FunctionalInequalities.Analysis.Tensor.symmetrize n (d + (k + 1)) (2 * d) B‖ ≤ ‖SA‖ + ‖A - B‖ := by
      have : FunctionalInequalities.Analysis.Tensor.symmetrize n (d + (k + 1)) (2 * d) B =
          SA - FunctionalInequalities.Analysis.Tensor.symmetrize n (d + (k + 1)) (2 * d) (A - B) := by
        rw [symmetrize_sub]
        abel
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_symmetrize_le _ _))
    have h4 : (0 : ℝ) ≤ 4 ^ d := by positivity
    nlinarith
  have hsq : ‖A‖ ^ 2 ≤ 2 * (1 + 4 ^ d) ^ 2 * ‖A - B‖ ^ 2 + 2 * 16 ^ d * ‖SA‖ ^ 2 := by
    have h44 : ((4 : ℝ) ^ d) ^ 2 = 16 ^ d := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h := pow_le_pow_left₀ (norm_nonneg A) htri 2
    calc ‖A‖ ^ 2 ≤ ((1 + 4 ^ d) * ‖A - B‖ + 4 ^ d * ‖SA‖) ^ 2 := h
      _ ≤ 2 * ((1 + 4 ^ d) * ‖A - B‖) ^ 2 + 2 * (4 ^ d * ‖SA‖) ^ 2 := by
          nlinarith [sq_nonneg ((1 + 4 ^ d) * ‖A - B‖ - 4 ^ d * ‖SA‖)]
      _ = 2 * (1 + 4 ^ d) ^ 2 * ‖A - B‖ ^ 2 + 2 * 16 ^ d * ‖SA‖ ^ 2 := by
          rw [mul_pow, mul_pow, h44]
          ring
  -- the constants
  have e1 : 2 * 16 ^ d * ‖SA‖ ^ 2 ≤ (2 ^ 20 * M ^ 2 / C) ^ d * Y :=
    calc 2 * 16 ^ d * ‖SA‖ ^ 2 ≤ 2 * 16 ^ d * ((β / C) ^ d * Y) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 2 * 16 ^ d * β ^ d * Y / (C : ℝ) ^ d := by rw [div_pow]; ring
      _ ≤ (2 ^ 20 * M ^ 2) ^ d * Y / (C : ℝ) ^ d := by
          gcongr
          exact const_bound_one hβ hd
      _ = (2 ^ 20 * M ^ 2 / C) ^ d * Y := by rw [div_pow]; ring
  have e2 : 2 * (1 + 4 ^ d) ^ 2 * ‖A - B‖ ^ 2 ≤ (2 ^ 20 * M ^ 2) ^ d * R ^ (2 * d) * C * D :=
    calc 2 * (1 + 4 ^ d) ^ 2 * ‖A - B‖ ^ 2
        ≤ 2 * (1 + 4 ^ d) ^ 2 * (R ^ (2 * d) * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * M ^ (2 * d) * C * D)) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = (2 * (1 + 4 ^ d) ^ 2 * (4 * ((2 * d : ℕ) : ℝ) ^ 4 * M ^ (2 * d))) *
            (R ^ (2 * d) * C * D) := by ring
      _ ≤ (2 ^ 20 * M ^ 2) ^ d * (R ^ (2 * d) * C * D) :=
          mul_le_mul_of_nonneg_right (const_bound_two β hd) (by positivity)
      _ = (2 ^ 20 * M ^ 2) ^ d * R ^ (2 * d) * C * D := by ring
  have hfin : ‖A‖ ^ 2 ≤
      (2 ^ 20 * M ^ 2 / C) ^ d * Y + (2 ^ 20 * M ^ 2) ^ d * R ^ (2 * d) * C * D := by
    refine hsq.trans ?_
    rw [add_comm]
    exact add_le_add e1 e2
  exact hfin

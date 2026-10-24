-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_gen_apply_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:48:39.939294+00:00
-- url     : https://prove2.me/submissions/94d4e885-7435-4da8-b468-e722588e0193

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiff_tiltAverage_of_memLp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_expTilt_of_memLp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_succ_of_eq_inner_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tiltAverage_adjointComp_eq_408915f

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
omit [FiniteDimensional ℝ E] in
/-- Pairing the tilt average of a vector class `G ∈ L²(μ; E)` with `w` is the tilt average of the
scalar class `⟪w, G⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.inner_tiltAverage_Lp (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (G : Lp E 2 μ) (w z : E) :
    ⟪w, tiltAverage μ (⇑G) z⟫ = tiltAverage μ (⇑((innerSL ℝ w).compLpL 2 μ G)) z := by
  rw [tiltAverage_congr_ae μ ((innerSL ℝ w).coeFn_compLpL G) z]
  unfold tiltAverage
  simp only [innerSL_apply_apply]
  exact (integral_inner (integrable_expTilt_of_memLp_408915f μ hexp (Lp.memLp G) z) w).symm
/-- The tilt average of a vector class `G ∈ L²(μ; E)` is smooth. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_Lp (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (G : Lp E 2 μ) :
    ContDiff ℝ ∞ (tiltAverage μ (⇑G)) := by
  let b := stdOrthonormalBasis ℝ E
  have h : tiltAverage μ (⇑G) =
      fun z => ∑ i, tiltAverage μ (⇑((innerSL ℝ (b i)).compLpL 2 μ G)) z • b i := by
    funext z
    simp_rw [← inner_tiltAverage_Lp μ hexp G _ z]
    exact (b.sum_repr' _).symm
  rw [h]
  exact ContDiff.sum fun i _ =>
    (contDiff_tiltAverage_of_memLp_408915f μ hexp (Lp.memLp _)).smul contDiff_const
end Lp
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
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (m : Measure E) [m.IsAddHaarMeasure]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section NormedSpace
variable {G H : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] [NormedAddCommGroup H]
variable [NormedSpace ℝ H] [CompleteSpace H]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Tilt averages commute with continuous linear maps (for integrable functions). -/
theorem FunctionalInequalities.Analysis.BakryEmery.clm_apply_tiltAverage (μ : Measure E)
    {g : E → G} (hg : ∀ z, Integrable g (expTilt μ z)) (L : G →L[ℝ] H) :
    (fun z => L (tiltAverage μ g z)) = tiltAverage μ (fun x => L (g x)) := by
    funext z
    unfold tiltAverage
    exact (L.integral_comp_comm (hg z)).symm
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Taylor tensors commute with continuous linear maps. -/
theorem FunctionalInequalities.Analysis.BakryEmery.clm_comp_taylorTensor (μ : Measure E)
    {g : E → G} (hg : ∀ z, Integrable g (expTilt μ z)) (hF : ContDiff ℝ ∞ (tiltAverage μ g))
    (L : G →L[ℝ] H) (d : ℕ) :
    L.compContinuousMultilinearMap (taylorTensor μ g d) = taylorTensor μ (fun x => L (g x)) d := by
  have heq := clm_apply_tiltAverage μ hg L
  have hd : iteratedFDeriv ℝ d (fun z => L (tiltAverage μ g z)) 0 =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ d (tiltAverage μ g) 0) :=
    L.iteratedFDeriv_comp_left hF.contDiffAt
      (show (d : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [heq] at hd
  ext v
  simp [taylorTensor, hd]
end NormedSpace
end NormedSpace
end
end
end
end
end

section
noncomputable section
open scoped LinearPMap
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
/-- Points of the domain of `T†T` are points of the domain of `T`. -/
theorem FunctionalInequalities.Analysis.Semigroup.mem_domain_of_mem_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (x : (adjointComp T).domain) :
    (x : H₀) ∈ T.domain :=
  x.2.2
end
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
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
section General
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
/-- The total gradient agrees with `T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ T.domain) :
    weakGrad T u = T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total generator agrees with `T†T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu
variable [FiniteDimensional ℝ V]
end General
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff RealInnerProductSpace ENNReal
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
section Generator
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
/-- **BKL Lemma 3.6 on the generator domain**: for `ν = m.tilted (-U)` with `U ∈ C¹` and all
exponential moments, and `F ∈ D(A)`, `T_{d+1}(A F) = S_{d+1} T_d(T̄ F)` for every `d`, the
original index of `T_d(T̄ F)` placed after its `d` Taylor indices. -/
theorem FunctionalInequalities.KLS.LogConcave.taylorTensor_adjointComp_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (d : ℕ) :
    taylorTensor (ν : Measure V)
        (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F))
        (d + 1) =
      symmetrizeML (appendInner (taylorTensor (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) d)) :=
  taylorTensor_succ_of_eq_inner_408915f (ν : Measure V) (contDiff_tiltAverage_Lp _ hexp _)
    (funext fun z => tiltAverage_adjointComp_eq_408915f m hν hi hνU hU hexp F z) d
end Generator
end
end
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
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
section Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
/-- Pairing the vector Taylor tensor of `G ∈ L²(ν; V)` with `w` is the Taylor tensor of the scalar
class `⟪w, G⟫`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.innerSL_comp_taylorTensor_Lp
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (G : Lp V 2 (ν : Measure V)) (w : V) (d : ℕ) :
    (innerSL ℝ w).compContinuousMultilinearMap (taylorTensor (ν : Measure V) (⇑G) d) =
      taylorTensor (ν : Measure V) (⇑((innerSL ℝ w).compLp G)) d := by
  rw [taylorTensor_congr_ae _ ((innerSL ℝ w).coeFn_compLp G) d]
  exact clm_comp_taylorTensor _ (integrable_expTilt_of_memLp_408915f _ hexp (Lp.memLp G))
    (contDiff_tiltAverage_Lp _ hexp G) (innerSL ℝ w) d
end Generic
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
include hνU hU hexp in
/-- **BKL Lemma 3.6 in coordinates**: for `u ∈ D(A)`, the entry of `T_{d+1}(A u)` at the basis
vectors `e_{i_0}, …, e_{i_d}` is the average over the permutations `τ` of `d + 1` positions of the
entry of `T_d(∂_{i_{τ d}} u)` at `e_{i_{τ 0}}, …, e_{i_{τ (d-1)}}`. -/
theorem solution {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain)
    (d : ℕ) (i : Fin (d + 1) → Fin (Module.finrank ℝ V)) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑(FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u)) (d + 1) (fun p => stdOrthonormalBasis ℝ V (i p)) =
      ((d + 1).factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin (d + 1)),
        FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑(FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv T̄ (i (τ (Fin.last d))) u)) d
          (fun p => stdOrthonormalBasis ℝ V (i (τ (Fin.castSucc p)))) := by
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem _ hu, FunctionalInequalities.KLS.LogConcave.taylorTensor_adjointComp_eq m hν hi hνU (hU.of_le (by norm_num)) hexp
    ⟨u, hu⟩ d]
  simp only [FunctionalInequalities.Analysis.Tensor.symmetrizeML, smul_apply, sum_apply, ContinuousMultilinearMap.domDomCongr_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv, FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem _ (FunctionalInequalities.Analysis.Semigroup.mem_domain_of_mem_adjointComp_domain _ ⟨u, hu⟩),
    ← FunctionalInequalities.KLS.LogConcave.PoissonIterate.innerSL_comp_taylorTensor_Lp hexp]
  simp only [FunctionalInequalities.Analysis.Tensor.appendInner, ContinuousMultilinearMap.uncurryRight_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  exact real_inner_comm _ _

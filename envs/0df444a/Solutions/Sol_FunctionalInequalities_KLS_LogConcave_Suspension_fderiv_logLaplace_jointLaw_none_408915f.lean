-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.fderiv_logLaplace_jointLaw_none_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:09:30.886667+00:00
-- url     : https://prove2.me/submissions/643d2f9c-1e41-4b22-a033-81b2273e3bf6

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Basic
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiffOn_logLaplace_ball_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_408915f
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_f_abs_exponential_moment_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_graph_norm_moment_of_local_moments_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_jointLaw_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_joint_first_derivative_of_radii_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_logConcave_jointLaw_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_408915f

section
noncomputable section
open MeasureTheory Set Topology Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
open scoped ContDiff in
/-- **A log-concave law has a smooth logarithmic Laplace transform near `0`**: for some `r > 0`,
`∫ e^{r‖x‖} dν < ∞` and `Λ_ν` is `C^∞` on the ball of radius `r` (BKL p. 29, through the Borell
exponential moment and `contDiffOn_logLaplace_ball`). -/
theorem FunctionalInequalities.KLS.LogConcave.exists_integrable_exp_norm_contDiffOn_logLaplace {ν : ProbabilityMeasure E} (hν : KLS.LogConcave ν) :
    ∃ r : ℝ, 0 < r ∧ Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure E) ∧
      ContDiffOn ℝ ∞ (Analysis.BakryEmery.logLaplace (ν : Measure E)) (Metric.ball 0 r) := by
  obtain ⟨r, hr, hi⟩ := ((KLS.LogConcave.borel_iff ν).1 hν).exists_integrable_exp_norm_408915f
  exact ⟨r, hr, hi, Analysis.BakryEmery.contDiffOn_logLaplace_ball_408915f (ν : Measure E) hr hi⟩
end FiniteDimensional
end
end
end

section
noncomputable section
open MeasureTheory Set
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_408915f hνW hW hconv)
end
end
end
end
end

section
open MeasureTheory FunctionalInequalities.Probability.Line
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
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.Analysis.BakryEmery in
/-- **The joint law is log-concave** under (110) (BKL p. 28, "Then `W_N` is convex"): (109) from
`jointLaw_eq_tilted` and convexity of `W_N` from `logConcave_jointLaw_of_eq_tilted`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ}
    (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (hint : Integrable (fun x => Real.exp (-V x)))
    (h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) :
    KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n)) :=
  logConcave_jointLaw_of_eq_tilted_408915f V f hβ hV hf hVa hfM hN
    (jointLaw_eq_tilted_408915f V f hβ hV.continuous.measurable hf.continuous.measurable hint) h
open scoped ContDiff in
/-- **Local exponential moments and smoothness of `Λ_ν` under (110)** (BKL p. 29, "the logarithmic
Laplace transform is finite and smooth in a neighborhood of the origin"): for `μ = e^{-V}dx/Z` with
`∇²V ≥ a`, `f ∈ C²` with `‖∇²f‖ ≤ M` and `β M/√N ≤ a`, the joint law has an exponential moment
`e^{r‖p‖}` for some `r > 0` and `Λ_ν` is `C^∞` on the ball of radius `r`. The density (109) is
proved, not assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw {n N : ℕ}
    (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ} (hβ : 0 < β) (hV : ContDiff ℝ 2 V)
    (hf : ContDiff ℝ 2 f) (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (hint : Integrable (fun x => Real.exp (-V x))) :
    ∃ r : ℝ, 0 < r ∧
      Integrable (fun p => Real.exp (r * ‖p‖))
        (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N) ∧
      ContDiffOn ℝ ∞ (Analysis.BakryEmery.logLaplace
        (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) (Metric.ball 0 r) := by
  have : IsProbabilityMeasure (volume.tilted fun x => -V x) := isProbabilityMeasure_tilted hint
  have hp := isProbabilityMeasure_jointLaw_of_pos (volume.tilted fun x => -V x)
    hf.continuous.measurable hβ (sigma β) N
  exact (logConcave_jointLaw V f hβ hV hf hVa hfM hN hint hp).exists_integrable_exp_norm_contDiffOn_logLaplace
end
end
end
end
end

section
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
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
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace
/-- The graph law has an exponential moment when the joint law and `μ` do; no moment of `f` is
assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_from_joint {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r s : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) (hs : 0 < s)
    (hexp : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw μ f β (sigma β) N))
    (hxs : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) := by
  obtain ⟨a, ha, hfa⟩ := exists_f_abs_exponential_moment_408915f μ hf hβ hN hr hexp
  exact exists_graph_norm_moment_of_local_moments_408915f μ hf ha hs hfa hxs
end
end
end
end
end
end

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line
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
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology ContDiff
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology
/-- Source-path entry: graph moments are derived internally from the actual joint and mu radii. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_joint_first_derivative_neighborhood {n N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r s : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) (hs : 0 < s)
    (hjoint : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw μ f β (sigma β) N))
    (hμ : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : JointSpace N n, z none = 0 → ‖z‖ < δ →
      HasDerivAt (fun w : ℝ => logLaplace (jointLaw μ f β (sigma β) N)
          (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
        ((∑ i : Fin N, tiltAverage μ f
          (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by
  obtain ⟨rG, hrG, hgraph⟩ := exists_graph_norm_moment_from_joint μ hf hβ hN hr hs hjoint hμ
  refine ⟨min r rG, lt_min hr hrG, ?_⟩
  intro z hz0 hz
  exact joint_first_derivative_of_radii_408915f μ hf hβ hN hr hrG hjoint hgraph z hz0 hz
open FunctionalInequalities
open scoped ContDiff
/-- The actual source construction supplies both radii: no joint, graph or f moment premise.
This is the chosen-positive-N local germ (111), retaining the source condition (110). -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.source_joint_first_derivative {n N : ℕ}
    (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hNpos : 0 < N) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hint : Integrable (fun x => Real.exp (-V x)))
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hN : β / Real.sqrt N * M ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : JointSpace N n, z none = 0 → ‖z‖ < δ →
      HasDerivAt (fun w : ℝ => logLaplace
          (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)
          (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
        ((∑ i : Fin N, tiltAverage (volume.tilted fun x => -V x) f
          (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted fun x => -V x
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hint
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := ⟨μ, inferInstance⟩
  have hμlc : KLS.LogConcave ν :=
    KLS.LogConcave.logConcave_of_eq_tilted (ν := ν) rfl hV.continuous
      (convexOn_of_hessian_ge_408915f hV ha.le hVa)
  obtain ⟨s, hs, hμ, _⟩ := hμlc.exists_integrable_exp_norm_contDiffOn_logLaplace
  obtain ⟨r, hr, hjoint, _⟩ := exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw
    V f hβ hV hf hVa hfM hN hint
  exact exists_joint_first_derivative_neighborhood μ
    hf.continuous.measurable hβ hNpos hr hs hjoint hμ
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- **BKL (111)** for the source's chosen `N`. -/
theorem solution {n N : ℕ} (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    {a b' : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}
    (hβ : 0 < β) (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (h110 : β / Real.sqrt N * M ≤ a) :
    ∃ r > 0, ∀ z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n, ‖z‖ < r → z none = 0 →
      fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) z
          (EuclideanSpace.single none 1) =
        (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)⁻¹ *
          ∑ i, FunctionalInequalities.Analysis.BakryEmery.tiltAverage (hV.law : Measure _) f (WithLp.toLp 2 fun j => z (some (i, j))) := by
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hint : Integrable (fun x => Real.exp (-V x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hV.integrable_exp_neg
  obtain ⟨δ, hδ, h111⟩ := source_joint_first_derivative
    V f hV.pos hβ hN hV2 hf hint hV.lower hfM h110
  obtain ⟨r, hr, _, hcd⟩ := FunctionalInequalities.KLS.LogConcave.Suspension.exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw
    V f hβ hV2 hf hV.lower hfM h110 hint
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro z hz hz0
  have hzδ : ‖z‖ < δ := hz.trans_le (min_le_left δ r)
  have hzr : ‖z‖ < r := hz.trans_le (min_le_right δ r)
  have hdiff : DifferentiableAt ℝ
      (FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) z := by
    apply (hcd.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hzr))).differentiableAt
    simp
  let e0 : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none
  have hline : HasDerivAt (fun w : ℝ => w • e0 + z) e0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e0).add_const z
  have hF : HasFDerivAt (FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N))
      (fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)) z)
      ((fun w : ℝ => w • e0 + z) 0) := by simpa using hdiff.hasFDerivAt
  have hd := hF.comp_hasDerivAt 0 hline
  have heq := hd.unique (h111 z hz0 hzδ)
  have hμeq : (hV.law : Measure _) = volume.tilted (fun x => -V x) := rfl
  simpa only [hμeq, e0, EuclideanSpace.basisFun_apply, div_eq_mul_inv, mul_comm] using heq

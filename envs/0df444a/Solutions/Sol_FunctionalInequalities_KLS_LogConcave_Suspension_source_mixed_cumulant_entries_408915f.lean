-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.source_mixed_cumulant_entries_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:11:15.490976+00:00
-- url     : https://prove2.me/submissions/8f71ee5e-f83e-4952-aa45-fc03b6708ece

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
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_fderiv_logLaplace_jointLaw_none_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_jointLaw_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_logConcave_jointLaw_of_eq_tilted_408915f

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
open FunctionalInequalities
open scoped ContDiff
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- Local continuous-linear restriction of an iterated derivative. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.iteratedFDeriv_comp_clm_at {f : E → F} (L : G →L[ℝ] E)
    {x : G} {d : ℕ} (hf : ContDiffAt ℝ d f (L x)) :
    iteratedFDeriv ℝ d (f ∘ L) x =
      (iteratedFDeriv ℝ d f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf.contDiffOn' le_rfl (by simp)
  have hfU' : ContDiffOn ℝ d f U := by simpa using hfU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hfU' hU.uniqueDiffOn
    hpre.uniqueDiffOn hxU (i := d) le_rfl
  rw [iteratedFDerivWithin_of_isOpen d hpre hxU,
    iteratedFDerivWithin_of_isOpen d hU hxU] at h
  exact h
section FiniteIndex
variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
/-- Each summand sees only its own copy. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.iteratedFDeriv_copy_apply
    (f : E → F) (i : ι) (x : ι → E) {d : ℕ}
    (hf : ContDiffAt ℝ d f (x i)) (labels : Fin d → ι) (v : Fin d → E) :
    iteratedFDeriv ℝ d (fun y : ι → E => f (y i)) x
      (fun k => Pi.single (labels k) (v k)) =
      if ∀ k, labels k = i then iteratedFDeriv ℝ d f (x i) v else 0 := by
  classical
  have h := iteratedFDeriv_comp_clm_at
    (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E) (x := x) hf
  change iteratedFDeriv ℝ d
    (f ∘ (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E)) x _ = _
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.proj_apply]
  split_ifs with hi
  · congr 1
    funext k
    simp [hi k]
  · obtain ⟨k, hk⟩ := not_forall.mp hi
    exact (iteratedFDeriv ℝ d f (x i)).map_coord_zero k (by simp [Ne.symm hk])
/-- Positive-order derivatives select a single copy precisely when every label agrees.
Repeated labels and repeated vector directions are retained in the multilinear evaluation. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.iteratedFDeriv_sum_copies_select
    (f : ι → E → F) (x : ι → E) (d : ℕ) (k0 : Fin d)
    (hf : ∀ i, ContDiffAt ℝ d (f i) (x i))
    (labels : Fin d → ι) (v : Fin d → E) :
    iteratedFDeriv ℝ d (fun y : ι → E => ∑ i, f i (y i)) x
      (fun k => Pi.single (labels k) (v k)) =
      if ∀ k, labels k = labels k0 then
        iteratedFDeriv ℝ d (f (labels k0)) (x (labels k0)) v else 0 := by
  classical
  have hsum := iteratedFDeriv_fun_sum_apply (u := Finset.univ)
    (f := fun i (y : ι → E) => f i (y i)) (x := x) (n := d)
    (fun i _ => (hf i).comp x
      (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E).contDiff.contDiffAt)
  rw [hsum]
  simp only [sum_apply]
  simp_rw [iteratedFDeriv_copy_apply _ _ _ (hf _)]
  split_ifs with hsame
  · rw [Finset.sum_eq_single (labels k0)]
    · simp [hsame]
    · intro i _ hi
      have hnot : ¬ ∀ k, labels k = i := fun h => hi (h k0).symm
      simp [hnot]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have hnot : ¬ ∀ k, labels k = i := by
      intro hi
      exact hsame (fun k => (hi k).trans (hi k0).symm)
    simp [hnot]
end FiniteIndex
set_option autoImplicit false
open Filter Set
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Local exchange of the first two directions; all remaining directions are retained. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.iteratedFDeriv_swap_front_on {g : E → F} {U : Set E}
    (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v w : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) g x (Fin.cons v (Fin.cons w h)) =
      iteratedFDeriv ℝ (n + 2) g x (Fin.cons w (Fin.cons v h)) := by
  have hgat : ContDiffAt ℝ ∞ g x := (hg x hx).contDiffAt (hU.mem_nhds hx)
  have hd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ n g) x :=
    hgat.iteratedFDeriv_right (m := ∞) (by norm_cast)
  have ha : ContDiffAt ℝ ∞ (fun y => iteratedFDeriv ℝ n g y h) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F h).contDiff.contDiffAt.comp x hd
  have heq (a : E) :
      (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons a h)) =ᶠ[𝓝 x]
        fun y => fderiv ℝ (fun z => iteratedFDeriv ℝ n g z h) y a := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hd' := ((hg y hy).contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right
      (i := n) (m := ∞) (by norm_cast)
    simpa using (hd'.differentiableAt (by simp)).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons a h)
  have hleft :=
    (hgat.differentiableAt_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp)).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons v (Fin.cons w h))
  have hright :=
    (hgat.differentiableAt_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp)).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons w (Fin.cons v h))
  rw [hleft, hright]
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [(heq w).fderiv_eq, (heq v).fderiv_eq]
  rw [fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiableAt (by norm_num))
      (differentiableAt_const w),
    fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiableAt (by norm_num))
      (differentiableAt_const v)]
  simpa using (ha.isSymmSndFDerivAt (by simp; norm_cast)).eq v w
/-- Move the distinguished direction from the first to the last slot locally. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.iteratedFDeriv_cons_snoc_on {g : E → F} {U : Set E}
    (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) g x (Fin.cons v h) =
      iteratedFDeriv ℝ (n + 1) g x (Fin.snoc h v) := by
  induction n generalizing x with
  | zero =>
      congr 1
      ext i
      fin_cases i
      simp [Fin.snoc_zero]
  | succ n ih =>
      have hgat : ContDiffAt ℝ ∞ g x := (hg x hx).contDiffAt (hU.mem_nhds hx)
      rw [← Fin.cons_self_tail h]
      rw [iteratedFDeriv_swap_front_on hg hU n x hx v (h 0) (Fin.tail h)]
      rw [← Fin.cons_snoc_eq_snoc_cons]
      have heq :
          (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons v (Fin.tail h))) =ᶠ[𝓝 x]
            fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.snoc (Fin.tail h) v) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih y hy (Fin.tail h)
      rw [(hgat.differentiableAt_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp)).iteratedFDeriv_succ_apply_left',
        (hgat.differentiableAt_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp)).iteratedFDeriv_succ_apply_left']
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        congrArg (fun a : E →L[ℝ] F => a (h 0)) heq.fderiv_eq
/-- Derivatives of the local first directional derivative are mixed higher derivatives,
with the distinguished vector in the source's first slot. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.iteratedFDeriv_directional_on {g : E → F} {U : Set E}
    (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (d : ℕ) (x : E) (hx : x ∈ U) (v : E) (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun y => fderiv ℝ g y v) x h =
      iteratedFDeriv ℝ (d + 1) g x (Fin.cons v h) := by
  have hgat : ContDiffAt ℝ ∞ g x := (hg x hx).contDiffAt (hU.mem_nhds hx)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ g) x := hgat.fderiv_right (by simp)
  have heval := (ContinuousLinearMap.apply ℝ F v).iteratedFDeriv_comp_left hd
    (i := d) (by norm_cast; simp)
  have hs := iteratedFDeriv_cons_snoc_on hg hU d x hx v h
  have ht := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := g) (x := x) (Fin.snoc h v)
  simp only [Fin.init_snoc, Fin.snoc_last] at ht
  rw [ht] at hs
  have heval' : iteratedFDeriv ℝ d (fun y => fderiv ℝ g y v) x h =
      iteratedFDeriv ℝ d (fderiv ℝ g) x h v := by
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_def, ContinuousLinearMap.apply_apply] using
      congrArg (fun a : E [×d]→L[ℝ] F => a h) heval
  exact heval'.trans hs.symm
open scoped ContDiff Topology
open Filter Set
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
section FiniteIndex
variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
/-- Smoothness of a separated copy sum at zero implies smoothness of each summand at zero.
The other copies contribute only a constant after a single-copy linear restriction. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.contDiffAt_component_of_copy_sum
    (F : ι → E → ℝ) {d : ℕ}
    (hF : ContDiffAt ℝ d (fun y : ι → E => ∑ j, F j (y j)) 0) (i : ι) :
    ContDiffAt ℝ d (F i) 0 := by
  classical
  have hr : ContDiffAt ℝ d (fun t : E => ∑ j, F j ((Pi.single i t : ι → E) j)) 0 := by
    let L : E →L[ℝ] (ι → E) := ContinuousLinearMap.single ℝ (fun _ : ι => E) i
    have hF' : ContDiffAt ℝ d (fun y : ι → E => ∑ j, F j (y j)) (L 0) := by
      simpa using hF
    simpa [L, Function.comp_def] using hF'.comp 0 L.contDiff.contDiffAt
  let c : ℝ := ∑ j ∈ Finset.univ.erase i, F j 0
  have hsplit (t : E) : (∑ j, F j ((Pi.single i t : ι → E) j)) = c + F i t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [hji]
    · simp
  have hsub := hr.sub (contDiffAt_const (c := c))
  convert hsub using 1
  funext t
  rw [hsplit]
  ring
/-- A nonzero scalar multiple of a separated sum can be peeled without any integrability input. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.contDiffAt_component_of_scaled_copy_sum
    (F : ι → E → ℝ) {d : ℕ} {c : ℝ} (hc : c ≠ 0)
    (hF : ContDiffAt ℝ d (fun y : ι → E => c * ∑ j, F j (y j)) 0) (i : ι) :
    ContDiffAt ℝ d (F i) 0 := by
  have hprod := (contDiffAt_const (c := c⁻¹)).mul hF
  have hsum : ContDiffAt ℝ d (fun y : ι → E => ∑ j, F j (y j)) 0 := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hprod
  exact contDiffAt_component_of_copy_sum F hsum i
/-- Local (111) on a linear spatial slice implies the finite-copy mixed derivative rule. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.mixed_copies_from_first_derivative_germ
    (g : G → ℝ) (L : (ι → E) →L[ℝ] G) (e : G) (F : ι → E → ℝ)
    (c : ℝ) (x : ι → E) {U : Set G} (hU : IsOpen U) (hx : L x ∈ U)
    (hg : ContDiffOn ℝ ∞ g U) (d : ℕ) (k0 : Fin d)
    (hF : ∀ i, ContDiffAt ℝ d (F i) (x i))
    (hfirst : (fun y => fderiv ℝ g (L y) e) =ᶠ[𝓝 x]
      fun y => c * ∑ i, F i (y i)) (labels : Fin d → ι) (v : Fin d → E) :
    iteratedFDeriv ℝ (d + 1) g (L x)
      (Fin.cons e (fun k => L (Pi.single (labels k) (v k)))) =
      if ∀ k, labels k = labels k0 then
        c * iteratedFDeriv ℝ d (F (labels k0)) (x (labels k0)) v else 0 := by
  classical
  let q : Fin d → ι → E := fun k => Pi.single (labels k) (v k)
  have hgat : ContDiffAt ℝ ∞ g (L x) := (hg (L x) hx).contDiffAt (hU.mem_nhds hx)
  have hdirectional : ContDiffAt ℝ d (fun y => fderiv ℝ g y e) (L x) := by
    exact ((ContinuousLinearMap.apply ℝ ℝ e).contDiff.contDiffAt.comp (L x)
      (hgat.fderiv_right (m := ∞) (by simp))).of_le (by norm_cast; simp)
  have hrestrict := iteratedFDeriv_comp_clm_at L hdirectional
  have hrestrict' :
      iteratedFDeriv ℝ d (fun y => fderiv ℝ g (L y) e) x q =
        iteratedFDeriv ℝ d (fun y => fderiv ℝ g y e) (L x) (fun k => L (q k)) := by
    simpa only [Function.comp_def, ContinuousMultilinearMap.compContinuousLinearMap_apply]
      using congrArg (fun a => a q) hrestrict
  have hmixed := iteratedFDeriv_directional_on hg hU d (L x) hx e (fun k => L (q k))
  have heq := (hfirst.iteratedFDeriv ℝ d).self_of_nhds
  have hsum : ContDiffAt ℝ d (fun y : ι → E => ∑ i, F i (y i)) x := by
    exact ContDiffAt.sum (fun i _ => (hF i).comp x
      (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E).contDiff.contDiffAt)
  have hscale := iteratedFDeriv_const_smul_apply' (a := c) hsum
  have hscale' :
      iteratedFDeriv ℝ d (fun y : ι → E => c * ∑ i, F i (y i)) x q =
        c * iteratedFDeriv ℝ d (fun y : ι → E => ∑ i, F i (y i)) x q := by
    simpa only [smul_eq_mul, smul_apply] using
      congrArg (fun a => a q) hscale
  calc
    _ = iteratedFDeriv ℝ d (fun y => fderiv ℝ g (L y) e) x q :=
      (hrestrict'.trans hmixed).symm
    _ = iteratedFDeriv ℝ d (fun y : ι → E => c * ∑ i, F i (y i)) x q :=
      congrArg (fun a => a q) heq
    _ = c * iteratedFDeriv ℝ d (fun y : ι → E => ∑ i, F i (y i)) x q := hscale'
    _ = _ := by
      rw [iteratedFDeriv_sum_copies_select F x d k0 hF labels v]
      split_ifs <;> simp
end FiniteIndex
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.jointSpatialSlice_single {N n : ℕ} (i : Fin N) (j : Fin n) :
    FunctionalInequalities.KLS.LogConcave.Suspension.jointSpatialSlice N n (Pi.single i (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      EuclideanSpace.single (some (i, j)) 1 := by
  ext o
  cases o with
  | none => simp
  | some ij =>
      rcases ij with ⟨i', j'⟩
      by_cases hi : i' = i
      · subst i'
        simp [EuclideanSpace.basisFun_apply]
      · simp [hi, EuclideanSpace.basisFun_apply, Prod.ext_iff]
open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace ContDiff Topology
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- BKL (112), derived from actual local (111), local smoothness of the actual joint log-Laplace,
and the finite-copy derivative selection rule. The same-copy tensor retains all repeated slots. -/
 theorem solution {n N : ℕ} (hN : 0 < N)
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b')
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ} (hβ : 0 < β)
    (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (h110 : β / Real.sqrt N * M ≤ a)
    {d : ℕ} (hd : 1 ≤ d) (I : Fin d → Fin N) (J : Fin d → Fin n) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw (hV.law : Measure _) f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N) (d + 1)
      (Fin.cons (EuclideanSpace.single none 1)
        (fun k => EuclideanSpace.single (some (I k, J k)) 1)) =
      if ∀ k k', I k = I k' then
        (d.factorial : ℝ) / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) *
          FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure _) f d
            (fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) else 0 := by
  classical
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := hV.law
  let ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) := FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N
  let L := FunctionalInequalities.KLS.LogConcave.Suspension.jointSpatialSlice N n
  let k0 : Fin d := ⟨0, by omega⟩
  have hμeq : μ = volume.tilted (fun x => -V x) := rfl
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨r, hr, _, hcd⟩ := FunctionalInequalities.KLS.LogConcave.Suspension.exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw
    V f hβ hV2 hf hV.lower hfM h110 hV.integrable_exp_neg
  have hcd' : ContDiffOn ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) (Metric.ball 0 r) := by
    simpa only [ν, hμeq] using hcd
  obtain ⟨δ, hδ, h111⟩ := FunctionalInequalities.KLS.LogConcave.Suspension.fderiv_logLaplace_jointLaw_none_408915f
    hN V hV hβ hf hfM h110
  have hfirst :
      (fun y => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) (L y) (EuclideanSpace.single none 1)) =ᶠ[𝓝 0]
        fun y : Fin N → EuclideanSpace ℝ (Fin n) =>
          (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)⁻¹ * ∑ i, FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f (y i) := by
    have hpre : L ⁻¹' Metric.ball 0 δ ∈ 𝓝 0 :=
      (Metric.isOpen_ball.preimage L.continuous).mem_nhds (by simp [hδ])
    filter_upwards [hpre] with y hy
    have hyδ : ‖L y‖ < δ := by simpa using hy
    have heq := h111 (L y) hyδ (FunctionalInequalities.KLS.LogConcave.Suspension.jointSpatialSlice_none y)
    simpa only [ν, μ, L, FunctionalInequalities.KLS.LogConcave.Suspension.jointSpatialSlice_some, WithLp.toLp_ofLp] using heq
  have hF : ∀ i : Fin N, ContDiffAt ℝ d (FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f) ((0 : Fin N → EuclideanSpace ℝ (Fin n)) i) := by
    intro i
    have hgat : ContDiffAt ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) (L 0) := by
      simpa using hcd'.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))
    have hdir : ContDiffAt ℝ d
        (fun y => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) (L y) (EuclideanSpace.single none 1)) 0 := by
      have hdirinf : ContDiffAt ℝ ∞
          (fun y => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) (L y) (EuclideanSpace.single none 1)) 0 := by
        simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
          ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single none 1)).contDiff.contDiffAt.comp
            (L 0) (hgat.fderiv_right (m := ∞) (by simp))).comp 0 L.contDiff.contDiffAt
      exact hdirinf.of_le (by norm_cast; simp)
    have hscaled : ContDiffAt ℝ d
        (fun y : Fin N → EuclideanSpace ℝ (Fin n) =>
          (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)⁻¹ * ∑ j, FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f (y j)) 0 :=
      hdir.congr_of_eventuallyEq hfirst.symm
    have hσ : 0 < FunctionalInequalities.KLS.LogConcave.Suspension.sigma β := by
      apply Real.sqrt_pos.mpr
      positivity
    have hc : (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero hσ.ne' (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne')
    exact contDiffAt_component_of_scaled_copy_sum (fun _ : Fin N => FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f) hc hscaled i
  have hmixed := mixed_copies_from_first_derivative_germ (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) L
    (EuclideanSpace.single none 1) (fun _ : Fin N => FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f)
    ((FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)⁻¹) 0 Metric.isOpen_ball
    (by simpa using hr) hcd' d k0 hF hfirst I
    (fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
  have hsame : (∀ k, I k = I k0) ↔ (∀ k k', I k = I k') := by
    constructor
    · intro h k k'
      exact (h k).trans (h k').symm
    · intro h k
      exact h k k0
  simp only [L, map_zero, jointSpatialSlice_single, Pi.zero_apply, hsame] at hmixed
  change iteratedFDeriv ℝ (d + 1) (FunctionalInequalities.Analysis.BakryEmery.logLaplace ν) 0 _ = _
  rw [hmixed]
  split_ifs
  · have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    simp only [FunctionalInequalities.Analysis.BakryEmery.taylorTensor, smul_apply, smul_eq_mul, div_eq_mul_inv]
    field_simp [hfac]
    rfl
  · rfl

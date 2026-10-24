-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_isotropic_localSlope_constant_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:43:46.750382+00:00
-- url     : https://prove2.me/submissions/58d6dab7-eb91-4225-bc4b-0a78e6d38fd9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Statement
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
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
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
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
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Covariance_intrinsic_operator_inner_self_pos_408915f
import Theorems.Thm_FunctionalInequalities_Covariance_operator_map_continuousLinearEquiv_408915f
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_eq_ofLinearPMap_408915f
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_mapContinuousLinearEquiv_408915f
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_translateLaw_408915f
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_ambient_extension_408915f
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_memLp_id_two_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_of_continuousLinearEquiv_map_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_L2Energy_constant_eq_of_linearIsometryEquiv_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_constant_eq_lipschitz_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_localSlope_408915f
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_408915f
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_mapContinuousLinearEquiv_408915f
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_translateLaw_408915f
import Theorems.Thm_FunctionalInequalities_exists_whitening_of_isSymmetric_408915f

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : ProbabilityMeasure V) (c : V)
variable [CompleteSpace V]
/-- Translation does not change the covariance operator. -/
theorem FunctionalInequalities.Covariance.operator_translateLaw :
    Covariance.operator (Probability.translateLaw ν c : Measure V) = Covariance.operator (ν : Measure V) := by
  unfold Covariance.operator
  rw [Probability.coe_translateLaw, ProbabilityTheory.covarianceBilin_map_const_add]
end Translation
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
omit [SecondCountableTopology V₁] in
/-- The covariance operator of the image law. -/
theorem FunctionalInequalities.Covariance.operator_mapContinuousLinearEquiv :
    Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp
        (T : V₁ →L[ℝ] V₂).adjoint :=
  Covariance.operator_map_continuousLinearEquiv_408915f (ν : Measure V₁) T
omit [SecondCountableTopology V₁] in
/-- The barycenter of the image law is the image of the barycenter. -/
theorem FunctionalInequalities.Probability.integral_id_mapContinuousLinearEquiv (hint : Integrable id (ν : Measure V₁)) :
    ∫ y, y ∂(Probability.mapContinuousLinearEquiv ν T : Measure V₂) = T (∫ x, x ∂(ν : Measure V₁)) := by
  rw [Probability.coe_mapContinuousLinearEquiv, integral_map T.continuous.measurable.aemeasurable
    continuous_id'.aestronglyMeasurable]
  have hint' : Integrable (fun x : V₁ ↦ x) (ν : Measure V₁) := hint
  exact (T : V₁ →L[ℝ] V₂).integral_comp_comm hint'
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] in
/-- The image law keeps a finite second moment. -/
theorem FunctionalInequalities.Probability.memLp_id_two_mapContinuousLinearEquiv (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) := by
  rw [Probability.coe_mapContinuousLinearEquiv, memLp_map_measure_iff aestronglyMeasurable_id
    T.continuous.measurable.aemeasurable]
  exact (T : V₁ →L[ℝ] V₂).comp_memLp' h
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
omit [CompleteSpace V₁] [CompleteSpace V₂] [FiniteDimensional ℝ V₁] in
/-- A full affine support stays full under a continuous linear equivalence. -/
theorem FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_eq_top (h : affineSupport ν = ⊤) :
    affineSupport (mapContinuousLinearEquiv ν T) = ⊤ := by
  rw [affineSupport_mapContinuousLinearEquiv_408915f, h]
  exact AffineMap.map_top_of_surjective _ T.surjective
end ContinuousLinearEquiv
end
end
end

section
noncomputable section
open MeasureTheory Set Topology
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
/-- Log-concavity is retained on the direction of the affine support, even for singular
ambient laws and a zero-dimensional carrier. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsicMeasure {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    LogConcave (Probability.intrinsicMeasure μ) :=
  hμ.of_affineIsometry_map (Probability.intrinsicMeasure μ) (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ).map_eq
omit [CompleteSpace E] in
/-- The intrinsic support has nonempty interior. This includes the singleton topology in
dimension zero and does not assert that the boundary has zero probability mass. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_intrinsic_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    (interior (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support).Nonempty := by
  apply hμ.intrinsicMeasure.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr
  exact Probability.affineSupport_intrinsicMeasure_408915f μ
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Metric Set Topology
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
section Intrinsic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]
omit [CompleteSpace F] in
/-- Every compact-set log-concave probability law is absolutely continuous in its own affine
support coordinates. Singular ambient measures and the zero-dimensional support are included. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m :=
  hμ.intrinsicMeasure.absolutelyContinuous_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty
end Intrinsic
end
end
end
end
end

section
noncomputable section
open MeasureTheory Set Topology Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section Intrinsic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
omit [CompleteSpace F] in
/-- The intrinsic law of a log-concave probability has an exponential moment: some positive
rate `t` makes `exp (t ‖v‖)` integrable. This is the tail estimate behind the moment
conclusion and is stated separately because it is the form proved in the literature. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_integrable_exp_norm {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖))
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) :=
  ((borel_iff _).1 hμ.intrinsicMeasure).exists_integrable_exp_norm_408915f
omit [CompleteSpace F] in
/-- The intrinsic law of a log-concave probability has finite moments of every order.
It follows from the exponential moment and Mathlib's `IntegrableExpMul`. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_integrable_norm_pow {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (p : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ p)
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) := by
  obtain ⟨t, ht, hint⟩ := hμ.intrinsic_integrable_exp_norm
  exact Probability.integrable_norm_pow_of_integrable_exp_norm ht hint p
end
end
end Intrinsic
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
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem FunctionalInequalities.L2.center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))
/-- Coercing the `NNReal` variance to `ℝ` gives the squared norm of the centered part. -/
@[simp, norm_cast]
theorem FunctionalInequalities.L2.coe_variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ‖center μ f‖ ^ 2 := by
  rfl
/-- The intrinsic `L²` variance agrees, after coercion, with Mathlib's variance of the
representative supplied by the `Lp` element. -/
theorem FunctionalInequalities.L2.coe_variance_eq_pointwise (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ProbabilityTheory.variance f (μ : Measure α) := by
  rw [coe_variance, ← real_inner_self_eq_norm_sq (center μ f),
    MeasureTheory.L2.inner_def,
    ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  apply integral_congr_ae
  filter_upwards [center_coeFn μ f] with x hx
  rw [hx, mean_eq_integral]
  simp [Real.norm_eq_abs]
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
universe u v
section
namespace FunctionalInequalities.L2.Translation
end FunctionalInequalities.L2.Translation
open FunctionalInequalities FunctionalInequalities.L2 FunctionalInequalities.L2.Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : ProbabilityMeasure V) (c : V)
omit [InnerProductSpace ℝ V] in
theorem FunctionalInequalities.L2.Translation.pullback_coeFn (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    pullback ν c f =ᵐ[(ν : Measure V)] fun x ↦ f (c + x) :=
  Lp.coeFn_compMeasurePreserving f (Probability.measurePreserving_translate ν c)
omit [InnerProductSpace ℝ V] in
/-- Pullback along the translation preserves the intrinsic `L²` variance. -/
theorem FunctionalInequalities.L2.Translation.variance_pullbackEquiv
    (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    L2.variance ν (pullbackEquiv ν c f) = L2.variance (Probability.translateLaw ν c) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, pullbackEquiv_apply,
    ProbabilityTheory.variance_congr (pullback_coeFn ν c f)]
  exact (Probability.measurePreserving_translate ν c).variance_fun_comp
    (Lp.aestronglyMeasurable f).aemeasurable
end
section
namespace FunctionalInequalities.L2.ContinuousLinearEquiv
end FunctionalInequalities.L2.ContinuousLinearEquiv
open FunctionalInequalities FunctionalInequalities.L2 FunctionalInequalities.L2.ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
theorem FunctionalInequalities.L2.ContinuousLinearEquiv.pullback_coeFn (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    pullback ν T f =ᵐ[(ν : Measure V₁)] fun x ↦ f (T x) :=
  Lp.coeFn_compMeasurePreserving f (Probability.measurePreserving_mapContinuousLinearEquiv ν T)
/-- Pullback along `T` preserves the intrinsic `L²` variance. -/
theorem FunctionalInequalities.L2.ContinuousLinearEquiv.variance_pullbackEquiv
    (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    L2.variance ν (pullbackEquiv ν T f) = L2.variance (Probability.mapContinuousLinearEquiv ν T) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, pullbackEquiv_apply,
    ProbabilityTheory.variance_congr (pullback_coeFn ν T f)]
  exact (Probability.measurePreserving_mapContinuousLinearEquiv ν T).variance_fun_comp
    (Lp.aestronglyMeasurable f).aemeasurable
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
include hμ in
/-- The intrinsic law of a log-concave probability has a finite second moment, so its
covariance operator is the genuine centered covariance. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_memLp_id_two :
    MemLp id 2
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) := by
  rw [memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id]
  simpa using hμ.intrinsic_integrable_norm_pow 2
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
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.CovarianceGradient
end FunctionalInequalities.Poincare.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.CovarianceGradient
open Energy.CovarianceGradient
universe u v
section Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V]
  (ν : ProbabilityMeasure V) (c : V)
/-- The optimal `L²` Poincaré constant of the covariance relaxation is translation invariant. -/
theorem FunctionalInequalities.Poincare.CovarianceGradient.constant_translateLaw :
    Poincare.L2Energy.constant (Probability.translateLaw ν c) (relaxation (Probability.translateLaw ν c)) =
      Poincare.L2Energy.constant ν (relaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_408915f ν (Probability.translateLaw ν c)
    (relaxation ν) (relaxation (Probability.translateLaw ν c)) (L2.Translation.pullbackEquiv ν c)
    (L2.Translation.variance_pullbackEquiv ν c) (relaxation_translateLaw_408915f ν c)
end Translation
section LinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂]
  (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
omit [SecondCountableTopology V₁] in
/-- The optimal `L²` Poincaré constant of the covariance relaxation is invariant under continuous
linear equivalences. -/
theorem FunctionalInequalities.Poincare.CovarianceGradient.constant_mapContinuousLinearEquiv :
    Poincare.L2Energy.constant (Probability.mapContinuousLinearEquiv ν T) (relaxation (Probability.mapContinuousLinearEquiv ν T)) =
      Poincare.L2Energy.constant ν (relaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_408915f ν (Probability.mapContinuousLinearEquiv ν T)
    (relaxation ν) (relaxation (Probability.mapContinuousLinearEquiv ν T)) (L2.ContinuousLinearEquiv.pullbackEquiv ν T)
    (L2.ContinuousLinearEquiv.variance_pullbackEquiv ν T) (relaxation_mapContinuousLinearEquiv_408915f ν T)
end LinearEquiv
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
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.CovarianceGradient
end FunctionalInequalities.Poincare.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.CovarianceGradient
section
namespace FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic
end FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.CovarianceGradient FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
/-- Unfolding the affine constant exposes the generic `L²` optimizer of the intrinsic law at the
sequential relaxation of the covariance pre-energy. -/
theorem FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq (μ : ProbabilityMeasure E) :
    constant μ = L2Energy.constant (Probability.intrinsicMeasure μ)
      ((Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)).sequentialRelaxation) :=
  rfl
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
/-- Source: local order consequence of `constant` and Mathlib's `iInf_le_of_le`.
Every finite valid constant bounds the optimal constant from above. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_le {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    constant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl
/-- Source: local order consequence of `constant` and Mathlib's `le_iInf`.
A lower bound for every finite valid constant bounds the optimal constant from below. -/
theorem FunctionalInequalities.Poincare.SmoothTest.le_constant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, Holds μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ constant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient
open Euclidean
universe u
private theorem FunctionalInequalities.Energy.SmoothGradient.pullbackTest_energy_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
    (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
    (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) :
    (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).energy ≤ f.energy := by
  apply NNReal.coe_le_coe.mp
  calc
    _ ≤ ∫ x, ‖gradient f (φ x)‖ ^ 2 ∂(μ : Measure X) := by
      apply integral_mono (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).gradient_sq_integrable
        (hmp.integrable_comp_of_integrable f.gradient_sq_integrable)
      intro x
      exact pow_le_pow_left₀ (norm_nonneg _) (FunctionalInequalities.Energy.SmoothGradient.norm_gradient_comp_le f.contDiff hφ hlip x) 2
    _ = _ := by
      have h := integral_map hmp.measurable.aemeasurable
        (hmp.map_eq.symm ▸ f.gradient_sq_integrable.aestronglyMeasurable)
      simpa only [hmp.map_eq, Test.coe_energy] using h.symm
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)
section
namespace FunctionalInequalities.Energy.SmoothGradient.Test
end FunctionalInequalities.Energy.SmoothGradient.Test
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient FunctionalInequalities.Energy.SmoothGradient.Test
/-- Restriction has the expected `L²` realization and does not increase raw energy.
Source: the tangential-gradient projection argument in the local Blueprint comparison. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction (f : Energy.SmoothGradient.Test μ) :
    ∃ g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ),
      (∀ v, g v = f (Probability.reconstruct μ v)) ∧
      g.toL2 = toIntrinsicL2 μ f.toL2 ∧ g.energy ≤ f.energy := by
  let φ := Probability.reconstruct μ
  have hφ : ContDiff ℝ ∞ φ := φ.toContinuousAffineMap.contDiff
  let g := FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ φ.isometry.lipschitz
    (Probability.measurePreserving_reconstruct μ)
  exact ⟨g, fun _ ↦ rfl, rfl,
    pullbackTest_energy_le f φ hφ φ.isometry.lipschitz
      (Probability.measurePreserving_reconstruct μ)⟩
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- Step 6: equality of the infima of valid finite constants on this same coordinate space.
The subtype infimum is the existing Poincare.LocalSlope.Holds definition, without a second intrinsic map. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_localSlope_infimum (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) :
    constant (ν : Measure E) =
      ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal) := by
  apply le_antisymm
  · refine le_iInf fun C => ?_
    exact constant_le ((holds_iff_localSlope_408915f ν m hν C.1).mpr C.2)
  · apply le_constant
    intro C hC
    exact iInf_le_of_le ⟨C, (holds_iff_localSlope_408915f ν m hν C).mp hC⟩ le_rfl
/-- Smooth inequalities transport between the ambient law and its intrinsic law without
absolute continuity. Restriction decreases energy, while normal-constant extension preserves it. -/
private theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsicMeasure (μ : ProbabilityMeasure E) (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      Holds (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) (C : ℝ) := by
  let ν := Probability.intrinsicMeasure μ
  have hvar (f : Energy.SmoothGradient.Test μ)
      (g : Energy.SmoothGradient.Test ν)
      (heq : ∀ v, g v = f (Probability.reconstruct μ v)) :
      ProbabilityTheory.variance g.toFun (ν : Measure (Probability.affineSupport μ).direction) =
        ProbabilityTheory.variance f.toFun (μ : Measure E) := by
    calc
      _ = ProbabilityTheory.variance (fun v => f (Probability.reconstruct μ v))
          (ν : Measure (Probability.affineSupport μ).direction) :=
        congrArg (fun k => ProbabilityTheory.variance k (ν : Measure _)) (funext heq)
      _ = _ := (Probability.measurePreserving_reconstruct μ).variance_fun_comp
        f.contDiff.continuous.aemeasurable
  constructor
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro g hg
    let gt : Energy.SmoothGradient.Test ν :=
      ⟨g, hg.smooth', hg.memLp_two, hg.energy_integrable⟩
    obtain ⟨f, heq, _, henergy⟩ :=
      Energy.SmoothGradient.Test.exists_ambient_extension_408915f μ gt
    have he : energy (μ : Measure E) f.toFun = energy (ν : Measure _) gt.toFun :=
      congrArg (fun c : NNReal => (c : ℝ)) henergy
    change ProbabilityTheory.variance gt.toFun (ν : Measure _) ≤ C * energy (ν : Measure _) gt.toFun
    rw [hvar f gt (fun v => (heq v).symm), ← he]
    exact h.variance_le ⟨f.contDiff, f.memLp_two, f.gradient_sq_integrable⟩
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    let ft : Energy.SmoothGradient.Test μ :=
      ⟨f, hf.smooth', hf.memLp_two, hf.energy_integrable⟩
    obtain ⟨g, heq, _, henergy⟩ :=
      Energy.SmoothGradient.Test.exists_intrinsic_restriction μ ft
    have he : energy (ν : Measure _) g.toFun ≤ energy (μ : Measure E) ft.toFun :=
      NNReal.coe_le_coe.mpr henergy
    have hb := h.variance_le ⟨g.contDiff, g.memLp_two, g.gradient_sq_integrable⟩
    change ProbabilityTheory.variance ft.toFun (μ : Measure E) ≤ C * energy (μ : Measure E) ft.toFun
    rw [← hvar ft g heq]
    exact hb.trans (mul_le_mul_of_nonneg_left he C.2)
/-- Step 7: the exact ambient / intrinsic / literature chain from the Blueprint theorem.
Use the proved smooth-test restriction and normal-constant extension for the first equality.
The Haar reference lives on the direction of the affine support; zero dimension is included. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (hμ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m) :
    constant (μ : Measure E) =
        constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ := by
  constructor
  · apply le_antisymm
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mpr hC)
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mp hC)
  · exact constant_eq_localSlope_infimum (Probability.intrinsicMeasure μ) m hμ
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]
section Bridge
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
/-- With identity covariance, the covariance relaxation of `def:affine-poincare-constant` is the
Lipschitz gradient relaxation. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_lipschitz (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hcov : Covariance.operator (ν : Measure V) = ContinuousLinearMap.id ℝ V) :
    relaxation ν = Energy.LipschitzGradient.relaxation ν m hac :=
  relaxation_eq_ofLinearPMap_408915f ν (ContinuousLinearMap.id ℝ V) hac hfr
    (fun v ↦ by rw [hcov, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq])
end
end
end Bridge
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
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- The ambient smooth-test, intrinsic smooth-test, and intrinsic literature optima agree
for every log-concave probability law. Absolute continuity is derived, not assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_intrinsic_and_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothTest.constant (μ : Measure E) =
        Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ :=
  Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ Measure.addHaar
    (hμ.intrinsic_absolutelyContinuous Measure.addHaar)
/-- The smooth-test optimum equals the literature optimum for every log-concave law. -/
theorem FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothTest.constant (μ : Measure E) = Poincare.LocalSlope.Intrinsic.constant μ :=
  (smoothTest_constant_eq_intrinsic_and_localSlope hμ).1.trans
    (smoothTest_constant_eq_intrinsic_and_localSlope hμ).2
end
end
end
end
end

section
noncomputable section
open InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
section
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities FunctionalInequalities.Covariance
variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
/-- A positive definite covariance operator has a self-adjoint whitening `W` with
`⟪Σ (W u), W v⟫ = ⟪u, v⟫`, so that `W ∘ Σ ∘ W = 1`. -/
theorem FunctionalInequalities.Covariance.exists_whitening (μ : MeasureTheory.Measure V)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ (operator μ v) v) :
    ∃ W : V ≃L[ℝ] V, (W : V →L[ℝ] V).adjoint = W ∧
      ∀ u v, inner ℝ (operator μ (W u)) (W v) = inner ℝ u v := by
  refine exists_whitening_of_isSymmetric_408915f (operator μ) ?_ hpos
  intro x y
  calc inner ℝ (operator μ x) y = ProbabilityTheory.covarianceBilin μ x y := operator_inner μ x y
    _ = ProbabilityTheory.covarianceBilin μ y x := ProbabilityTheory.covarianceBilin_comm x y
    _ = inner ℝ (operator μ y) x := (operator_inner μ y x).symm
    _ = inner ℝ x (operator μ y) := real_inner_comm _ _
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
open Energy Energy.Euclidean Probability
section Euclidean
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [CompleteSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂] in
/-- The image of a log-concave law under a continuous linear equivalence is log-concave. -/
theorem FunctionalInequalities.KLS.LogConcave.mapContinuousLinearEquiv {ν : ProbabilityMeasure V₁} (hν : LogConcave ν) (T : V₁ ≃L[ℝ] V₂) :
    LogConcave (Probability.mapContinuousLinearEquiv ν T) :=
  hν.of_continuousLinearEquiv_map_408915f _ T.symm (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T).map_eq
end
end
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] in
omit [InnerProductSpace ℝ V₁] in
/-- Translation keeps a finite second moment. -/
theorem FunctionalInequalities.Probability.memLp_id_two_translateLaw
    (ν : ProbabilityMeasure V₁) (c : V₁) (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (translateLaw ν c : Measure V₁) := by
  rw [coe_translateLaw]
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr ((memLp_const c).add h)
end
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
omit [CompleteSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] in
/-- A log-concave law with full affine support has support with nonempty interior. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_affineSupport_eq_top {ν : ProbabilityMeasure V₁}
    (hν : LogConcave ν) (h : affineSupport ν = ⊤) :
    (interior (ν : Measure V₁).support).Nonempty :=
  hν.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr h
end
end
end Euclidean
section Statements
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
omit [CompleteSpace E] in
/-- The centered and whitened intrinsic law of a log-concave law: there is an isotropic log-concave
law on the direction space with the same affine covariance Poincaré constant, equal to its literature
constant. -/
theorem solution {μ : ProbabilityMeasure E}
    (hμ : FunctionalInequalities.KLS.LogConcave μ) :
    ∃ ν' : ProbabilityMeasure (FunctionalInequalities.Probability.affineSupport μ).direction,
      FunctionalInequalities.KLS.LogConcave ν' ∧ FunctionalInequalities.KLS.Isotropic ν' ∧ FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ = FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν' := by
  set ν := FunctionalInequalities.Probability.intrinsicMeasure μ with hνdef
  have hν : FunctionalInequalities.KLS.LogConcave ν := hμ.intrinsicMeasure
  have hν2 : MemLp id 2 (ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) := hμ.intrinsic_memLp_id_two
  have hpos : ∀ v : (FunctionalInequalities.Probability.affineSupport μ).direction, v ≠ 0 →
      0 < inner ℝ (FunctionalInequalities.Covariance.operator (ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) v) v :=
    fun v hv ↦ FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos_408915f μ hμ.memLp_id_two_408915f hv
  obtain ⟨W, hWadj, hW⟩ := FunctionalInequalities.Covariance.exists_whitening (ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) hpos
  set c : (FunctionalInequalities.Probability.affineSupport μ).direction := -∫ x, x ∂(ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) with hcdef
  set νc := FunctionalInequalities.Probability.translateLaw ν c with hνc
  set νt := FunctionalInequalities.Probability.mapContinuousLinearEquiv νc W with hνt
  have hνc_lc : FunctionalInequalities.KLS.LogConcave νc := hν.translateLaw c
  have hνt_lc : FunctionalInequalities.KLS.LogConcave νt := hνc_lc.mapContinuousLinearEquiv W
  have hνc2 : MemLp id 2 (νc : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) := FunctionalInequalities.Probability.memLp_id_two_translateLaw ν c hν2
  have hνt2 : MemLp id 2 (νt : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) := FunctionalInequalities.Probability.memLp_id_two_mapContinuousLinearEquiv νc W hνc2
  have hmean_c : ∫ x, x ∂(νc : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) = 0 :=
    FunctionalInequalities.Probability.integral_id_translateLaw_neg_integral ν (hν2.integrable one_le_two)
  have hmean_t : ∫ y, y ∂(νt : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) = 0 := by
    rw [hνt, FunctionalInequalities.Probability.integral_id_mapContinuousLinearEquiv νc W (hνc2.integrable one_le_two), hmean_c, map_zero]
  have hcov_c : FunctionalInequalities.Covariance.operator (νc : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) = FunctionalInequalities.Covariance.operator (ν : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) :=
    FunctionalInequalities.Covariance.operator_translateLaw ν c
  have hcov_t : FunctionalInequalities.Covariance.operator (νt : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) = ContinuousLinearMap.id ℝ _ := by
    rw [hνt, FunctionalInequalities.Covariance.operator_mapContinuousLinearEquiv, hcov_c, hWadj]
    refine ContinuousLinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [← hWadj, ContinuousLinearMap.adjoint_inner_left, hWadj]
    exact hW u v
  have hiso : FunctionalInequalities.KLS.Isotropic νt := ⟨hνt2, hmean_t, hcov_t⟩
  -- full support of the whitened law
  have htop : FunctionalInequalities.Probability.affineSupport νt = ⊤ := by
    apply FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_eq_top
    rw [hνc, FunctionalInequalities.Probability.affineSupport_translateLaw_408915f, FunctionalInequalities.Probability.affineSupport_intrinsicMeasure_408915f]
    exact AffineMap.map_top_of_surjective _ (AffineEquiv.constVAdd ℝ _ c).surjective
  have hi : (interior (νt : Measure (FunctionalInequalities.Probability.affineSupport μ).direction).support).Nonempty :=
    hνt_lc.interior_support_nonempty_of_affineSupport_eq_top htop
  have hac : (νt : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) ≪ (Measure.addHaar : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) :=
    hνt_lc.absolutelyContinuous_haar Measure.addHaar hi
  have hfr : (νt : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) (frontier (νt : Measure (FunctionalInequalities.Probability.affineSupport μ).direction).support) = 0 :=
    hνt_lc.frontier_support_eq_zero hi
  refine ⟨νt, hνt_lc, hiso, ?_⟩
  calc FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ
      = FunctionalInequalities.Poincare.L2Energy.constant ν (FunctionalInequalities.Energy.CovarianceGradient.relaxation ν) := FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq μ
    _ = FunctionalInequalities.Poincare.L2Energy.constant νc (FunctionalInequalities.Energy.CovarianceGradient.relaxation νc) :=
        (FunctionalInequalities.Poincare.CovarianceGradient.constant_translateLaw ν c).symm
    _ = FunctionalInequalities.Poincare.L2Energy.constant νt (FunctionalInequalities.Energy.CovarianceGradient.relaxation νt) :=
        (FunctionalInequalities.Poincare.CovarianceGradient.constant_mapContinuousLinearEquiv νc W).symm
    _ = FunctionalInequalities.Poincare.L2Energy.constant νt (FunctionalInequalities.Energy.LipschitzGradient.relaxation νt Measure.addHaar hac) := by
        rw [FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_lipschitz νt Measure.addHaar hac hfr hcov_t]
    _ = FunctionalInequalities.Poincare.SmoothTest.constant (νt : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) :=
        (FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz_408915f νt Measure.addHaar hac hfr).symm
    _ = FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant νt := hνt_lc.smoothTest_constant_eq_localSlope

-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.memLp_id_two_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:20:24.679338+00:00
-- url     : https://prove2.me/submissions/6d82b144-173f-410e-86c8-b77193c80fc8

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_BorelLogConcave_exists_integrable_exp_norm_408915f

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
section Coordinates
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Reconstruction is continuous. -/
theorem FunctionalInequalities.Probability.continuous_reconstruct (μ : ProbabilityMeasure E) : Continuous (reconstruct μ) :=
  (reconstruct μ).continuous
end Coordinates
end
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
open Energy.Euclidean Probability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E}
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
omit [CompleteSpace E] in
/-- A log-concave law has a finite ambient second moment: the intrinsic law has one and
reconstruction is an affine isometry. -/
theorem solution (hμ : FunctionalInequalities.KLS.LogConcave μ) : MemLp id 2 (μ : Measure E) := by
  have hν := hμ.intrinsic_memLp_id_two
  have h1 : MemLp (fun v ↦ FunctionalInequalities.Probability.reconstruct μ v) 2
      (FunctionalInequalities.Probability.intrinsicMeasure μ : Measure (FunctionalInequalities.Probability.affineSupport μ).direction) := by
    refine MemLp.of_le ((memLp_const ‖FunctionalInequalities.Probability.reconstruct μ 0‖).add hν.norm)
      (FunctionalInequalities.Probability.continuous_reconstruct μ).aestronglyMeasurable (Eventually.of_forall fun v ↦ ?_)
    change ‖FunctionalInequalities.Probability.reconstruct μ v‖ ≤ ‖‖FunctionalInequalities.Probability.reconstruct μ 0‖ + ‖v‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc ‖FunctionalInequalities.Probability.reconstruct μ v‖ = ‖(FunctionalInequalities.Probability.reconstruct μ v - FunctionalInequalities.Probability.reconstruct μ 0) + FunctionalInequalities.Probability.reconstruct μ 0‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖FunctionalInequalities.Probability.reconstruct μ v - FunctionalInequalities.Probability.reconstruct μ 0‖ + ‖FunctionalInequalities.Probability.reconstruct μ 0‖ := norm_add_le _ _
      _ = ‖v‖ + ‖FunctionalInequalities.Probability.reconstruct μ 0‖ := by
          rw [← dist_eq_norm, (FunctionalInequalities.Probability.reconstruct μ).dist_map, dist_zero_right]
      _ = ‖FunctionalInequalities.Probability.reconstruct μ 0‖ + ‖v‖ := add_comm _ _
  have h2 : MemLp (fun x ↦ FunctionalInequalities.Probability.reconstruct μ (FunctionalInequalities.Probability.intrinsicMap μ x)) 2 (μ : Measure E) := by
    rw [← (FunctionalInequalities.Probability.measurePreserving_intrinsicMap μ).map_eq] at h1
    exact (memLp_map_measure_iff (FunctionalInequalities.Probability.continuous_reconstruct μ).aestronglyMeasurable
      (FunctionalInequalities.Probability.measurable_intrinsicMap μ).aemeasurable).mp h1
  exact h2.ae_eq (FunctionalInequalities.Probability.reconstruct_intrinsicMap_ae μ)

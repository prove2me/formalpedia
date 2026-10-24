-- Prove2me | solution 1 for FunctionalInequalities.Energy.CovarianceGradient.relaxation_le_mul_lipschitz_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:52:29.856807+00:00
-- url     : https://prove2.me/submissions/a62ffaf4-ddc4-4e51-9680-88b10b73e470

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
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
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_eq_ofLinearPMap_408915f
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_sequentialRelaxation_comp_le_mul_408915f
import Theorems.Thm_FunctionalInequalities_exists_norm_sq_eq_inner_of_isSymmetric_408915f

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
/-- The covariance operator of any Borel measure has a norm factor `B` satisfying
`⟪Σ v, v⟫ = ‖B v‖²`, including the zero operator of laws without second moment and the
zero-dimensional space. -/
theorem FunctionalInequalities.Covariance.exists_inner_eq_norm_sq (μ : MeasureTheory.Measure V) :
    ∃ B : V →L[ℝ] V, ∀ v, inner ℝ (operator μ v) v = ‖B v‖ ^ 2 := by
  refine exists_norm_sq_eq_inner_of_isSymmetric_408915f (operator μ) ?_ ?_
  · intro x y
    calc inner ℝ (operator μ x) y = ProbabilityTheory.covarianceBilin μ x y := operator_inner μ x y
      _ = ProbabilityTheory.covarianceBilin μ y x := ProbabilityTheory.covarianceBilin_comm x y
      _ = inner ℝ (operator μ y) x := (operator_inner μ y x).symm
      _ = inner ℝ x (operator μ y) := real_inner_comm _ _
  · intro v
    rw [operator_inner]
    exact ProbabilityTheory.covarianceBilin_self_nonneg v
end
end
end
end

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
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities.Energy.CovarianceGradient in
/-- The covariance relaxation is at most the operator norm of the covariance times the Lipschitz
gradient relaxation, at every point of finite Lipschitz relaxation. -/
theorem solution (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) (f : Lp ℝ 2 (ν : Measure V))
    (hf : FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac f ≠ ⊤) :
    FunctionalInequalities.Energy.CovarianceGradient.relaxation ν f ≤
      (‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖₊ : ENNReal) * FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac f := by
  obtain ⟨B, hB⟩ := FunctionalInequalities.Covariance.exists_inner_eq_norm_sq (ν : Measure V)
  rw [FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap_408915f ν B hac hfr hB]
  refine FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul_408915f
    (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac) :
      FunctionalInequalities.Energy.PreEnergy (Lp ℝ 2 (ν : Measure V)))
    (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν B hac) : FunctionalInequalities.Energy.PreEnergy (Lp ℝ 2 (ν : Measure V))) id
    continuous_id ‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖₊ ?_ f hf
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (FunctionalInequalities.Energy.WeightedGradient.mem_domain_operator_iff ν _ hac x).mp hx
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [FunctionalInequalities.Energy.WeightedGradient.apply_id] using hg.memLp_apply
  have hgB : FunctionalInequalities.Energy.WeightedGradient.IsTest ν B g := ⟨hg.1, hg.memLp, B.comp_memLp' hgrad⟩
  refine ⟨⟨_, FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν B hac hgB⟩, rfl, ?_⟩
  rw [FunctionalInequalities.Energy.PreEnergy.ofLinearPMap_energy, FunctionalInequalities.Energy.PreEnergy.ofLinearPMap_energy,
    FunctionalInequalities.Energy.WeightedGradient.operator_apply ν B hac hfr hgB _ rfl,
    FunctionalInequalities.Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr hg hx rfl, ← ENNReal.coe_mul]
  apply ENNReal.coe_le_coe.mpr
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [FunctionalInequalities.L2.norm_toLp_sq, FunctionalInequalities.L2.norm_toLp_sq, FunctionalInequalities.Energy.WeightedGradient.apply_id, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _)
    (((memLp_two_iff_integrable_sq_norm hgrad.1).mp hgrad).const_mul _) (ae_of_all _ fun x ↦ ?_)
  change ‖B (gradient g x)‖ ^ 2 ≤ ‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ ^ 2
  rw [← hB]
  calc inner ℝ (FunctionalInequalities.Covariance.operator (ν : Measure V) (gradient g x)) (gradient g x)
      ≤ ‖FunctionalInequalities.Covariance.operator (ν : Measure V) (gradient g x)‖ * ‖gradient g x‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ * ‖gradient g x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ ^ 2 := by ring

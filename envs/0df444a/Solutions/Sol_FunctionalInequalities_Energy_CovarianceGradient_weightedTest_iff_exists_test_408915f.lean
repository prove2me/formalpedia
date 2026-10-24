-- Prove2me | solution 1 for FunctionalInequalities.Energy.CovarianceGradient.weightedTest_iff_exists_test_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:50:08.859088+00:00
-- url     : https://prove2.me/submissions/ebcbb65e-0854-4121-b449-e6a5708afc92

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
section Gradient
section Measurability
variable [MeasurableSpace V] [BorelSpace V]
section
namespace FunctionalInequalities.Energy.WeightedGradient
end FunctionalInequalities.Energy.WeightedGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
/-- The weighted gradient of any function is Borel measurable. -/
theorem FunctionalInequalities.Energy.WeightedGradient.measurable_apply (B : V →L[ℝ] V) (g : V → ℝ) :
    Measurable (apply B g) :=
  B.continuous.measurable.comp (LipschitzApproximation.measurable_gradient g)
end
end Measurability
end Gradient
section Operator
variable [MeasurableSpace V] (ν : ProbabilityMeasure V) (B : V →L[ℝ] V)
variable [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {m : Measure V} [m.IsAddHaarMeasure]
section
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.CovarianceGradient
open WeightedGradient
omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance density is the squared weighted gradient. -/
theorem FunctionalInequalities.Energy.CovarianceGradient.density_eq_norm_sq
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
    density ν g = fun x ↦ ‖apply B g x‖ ^ 2 := by
  funext x
  exact hB _
namespace FunctionalInequalities.Energy.CovarianceGradient
end FunctionalInequalities.Energy.CovarianceGradient
open FunctionalInequalities.Energy.CovarianceGradient in
omit [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance tests are exactly the gradient tests. -/
theorem solution
    (hB : ∀ v, inner ℝ (FunctionalInequalities.Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
    FunctionalInequalities.Energy.WeightedGradient.IsTest ν B g ↔ ∃ f : FunctionalInequalities.Energy.CovarianceGradient.Test ν, f.toFun = g := by
  have hmeas : AEStronglyMeasurable (FunctionalInequalities.Energy.WeightedGradient.apply B g) (ν : Measure V) :=
    (FunctionalInequalities.Energy.WeightedGradient.measurable_apply B g).aestronglyMeasurable
  constructor
  · rintro ⟨hK, h2, hBg⟩
    refine ⟨⟨g, hK, h2, ?_⟩, rfl⟩
    rw [FunctionalInequalities.Energy.CovarianceGradient.density_eq_norm_sq ν B hB]
    exact (memLp_two_iff_integrable_sq_norm hmeas).mp hBg
  · rintro ⟨f, rfl⟩
    refine ⟨f.lipschitz, f.memLp_two, ?_⟩
    rw [memLp_two_iff_integrable_sq_norm hmeas, ← FunctionalInequalities.Energy.CovarianceGradient.density_eq_norm_sq ν B hB]
    exact f.integrable

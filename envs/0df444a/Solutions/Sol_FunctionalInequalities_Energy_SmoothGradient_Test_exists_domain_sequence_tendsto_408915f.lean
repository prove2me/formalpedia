-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:56:12.977042+00:00
-- url     : https://prove2.me/submissions/8ef10105-27ad-4941-959b-170c5f0cbba0

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
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
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
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_LocalDensity_subset_support_408915f

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
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
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section
namespace FunctionalInequalities.Energy.SmoothGradient.LocalDensity
end FunctionalInequalities.Energy.SmoothGradient.LocalDensity
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient FunctionalInequalities.Energy.SmoothGradient.LocalDensity
variable {ν : ProbabilityMeasure V} {m : Measure V} (D : LocalDensity ν m)
variable [m.IsAddHaarMeasure]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- `Ω` lies in the interior of the support. -/
theorem FunctionalInequalities.Energy.SmoothGradient.LocalDensity.subset_interior_support : D.Ω ⊆ interior (ν : Measure V).support :=
  interior_maximal D.subset_support_408915f D.isOpen
omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
include D in
/-- The frontier of the support is `ν`-null. -/
theorem FunctionalInequalities.Energy.SmoothGradient.LocalDensity.frontier_support_null : (ν : Measure V) (frontier (ν : Measure V).support) = 0 := by
  refine measure_mono_null ?_ D.compl_null
  intro x hx hxΩ
  rw [Measure.isClosed_support.frontier_eq] at hx
  exact hx.2 (D.subset_interior_support hxΩ)
end
section Agreement
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure] (D : LocalDensity ν m)
open Energy.WeightedGradient Energy.Euclidean
namespace FunctionalInequalities.Energy.SmoothGradient.Test
end FunctionalInequalities.Energy.SmoothGradient.Test
open FunctionalInequalities.Energy.SmoothGradient.Test in
/-- Smooth cutoffs: every smooth test is the graph-norm limit of globally Lipschitz compactly
supported tests, as elements of the operator domain. -/
theorem solution (f : FunctionalInequalities.Energy.SmoothGradient.Test ν) :
    ∃ p : ℕ → (FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D).domain,
      Tendsto (fun j ↦ (((p j : (FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D).domain) : Lp ℝ 2 (ν : Measure V)),
        FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D (p j))) atTop
        (𝓝 (f.toL2, (FunctionalInequalities.Energy.SmoothGradient.Test.memLp_gradient ν f).toLp (gradient f.toFun))) := by
  have hac := D.absolutelyContinuous
  have hfr := D.frontier_support_null
  have hlip : LocallyLipschitz f.toFun := (f.contDiff.of_le (by exact_mod_cast le_top)).locallyLipschitz
  have hgrad : MemLp (fun x ↦ (ContinuousLinearMap.id ℝ V) (gradient f.toFun x)) 2 (ν : Measure V) := by
    simpa using FunctionalInequalities.Energy.SmoothGradient.Test.memLp_gradient ν f
  obtain ⟨g, hg, hconv1, hconv2⟩ := FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_compactSupport_weighted_L2 ν m hac
    (ContinuousLinearMap.id ℝ V) f.toFun hlip f.memLp_two hgrad
  have hIsTest : ∀ j, FunctionalInequalities.Energy.WeightedGradient.IsTest ν (ContinuousLinearMap.id ℝ V) (g j) := fun j ↦
    ⟨(hg j).2.1, (hg j).2.2.1, (hg j).2.2.2⟩
  refine ⟨fun j ↦ ⟨(hIsTest j).memLp.toLp (g j),
    FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V) hac (hIsTest j)⟩, ?_⟩
  have hT : ∀ j, FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D ⟨(hIsTest j).memLp.toLp (g j),
      FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V) hac (hIsTest j)⟩ =
      (hIsTest j).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) (g j)) := fun j ↦
    FunctionalInequalities.Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr (hIsTest j) _ rfl
  refine Filter.Tendsto.prodMk_nhds ?_ ?_
  · rw [tendsto_iff_dist_tendsto_zero]
    have h : ∀ j, dist ((hIsTest j).memLp.toLp (g j)) f.toL2 =
        (eLpNorm (fun x ↦ g j x - f.toFun x) 2 (ν : Measure V)).toReal := by
      intro j
      rw [dist_edist, FunctionalInequalities.Energy.SmoothGradient.Test.toL2, Lp.edist_toLp_toLp]
      rfl
    simp_rw [h]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv1
    simpa [Function.comp_def] using this
  · simp_rw [hT]
    rw [tendsto_iff_dist_tendsto_zero]
    have h : ∀ j, dist ((hIsTest j).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) (g j)))
        ((FunctionalInequalities.Energy.SmoothGradient.Test.memLp_gradient ν f).toLp (gradient f.toFun)) =
        (eLpNorm (fun x ↦ (ContinuousLinearMap.id ℝ V) (gradient (g j) x) -
          (ContinuousLinearMap.id ℝ V) (gradient f.toFun x)) 2 (ν : Measure V)).toReal := by
      intro j
      rw [dist_edist, Lp.edist_toLp_toLp]
      rfl
    simp_rw [h]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv2
    simpa [Function.comp_def] using this

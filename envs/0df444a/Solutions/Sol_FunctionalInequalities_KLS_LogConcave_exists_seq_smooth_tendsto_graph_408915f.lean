-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_graph_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:30:12.226613+00:00
-- url     : https://prove2.me/submissions/4def5585-fced-493f-b3d0-fce4d83569db

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
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
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
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
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Filter Topology
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
open Energy Energy.WeightedGradient FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Core
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **Smooth compactly supported classes are a graph-norm core of `T̄`.** Every `x ∈ D(T̄)` is the
`L²` limit of classes `[gₙ]` of smooth compactly supported functions whose weighted gradients
`[B ∇gₙ]` converge in `L²` to `T̄ x`. This is the sequential form of
`closure_domRestrict_eq_of_smoothCore_le`; it controls the function and its **first** derivative
only, and says nothing about any second-order quantity. -/
theorem solution (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ (g : ℕ → V → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hgc : ∀ n, HasCompactSupport (g n)),
      Tendsto (fun n => (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))
          atTop (𝓝 (x : Lp ℝ 2 (ν : Measure V))) ∧
        Tendsto (fun n => (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n)
            (hgc n)).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply B (g n))) atTop
          (𝓝 (hν.closedWeightedOperator m B hi x)) := by
  classical
  have hac : (ν : Measure V) ≪ m := hν.absolutelyContinuous_haar m hi
  have hScl : ((hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)).closure =
      hν.closedWeightedOperator m B hi :=
    hν.closure_domRestrict_eq_of_smoothCore_le m B hi le_rfl
      (FunctionalInequalities.Energy.WeightedGradient.smoothCore_le_domain_operator ν B hac)
  have hSc : ((hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)).IsClosable :=
    (hν.weightedOperator_isClosable m B hi).leIsClosable LinearPMap.domRestrict_le
  have hgraph : ((x : Lp ℝ 2 (ν : Measure V)), hν.closedWeightedOperator m B hi x)
      ∈ ((hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)).graph.topologicalClosure := by
    rw [hSc.graph_closure_eq_closure_graph, hScl]
    exact (hν.closedWeightedOperator m B hi).mem_graph x
  obtain ⟨f, hf⟩ :=
    (FunctionalInequalities.Energy.mem_graph_topologicalClosure_iff
      ((hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)) _).mp hgraph
  have hmem : ∀ n, ∃ (g : V → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g),
      (f n : Lp ℝ 2 (ν : Measure V))
        = (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hg hgc).toLp g :=
    fun n => (Submodule.mem_inf.mp (f n).2).1
  choose g hg hgc hgeq using hmem
  have hval : ∀ n, (hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν) (f n) =
      (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)).memLp_apply.toLp
        (FunctionalInequalities.Energy.WeightedGradient.apply B (g n)) := by
    intro n
    have hdom : (f n : Lp ℝ 2 (ν : Measure V)) ∈ (hν.weightedOperator m B hi).domain :=
      (Submodule.mem_inf.mp (f n).2).2
    erw [LinearPMap.domRestrict_apply (x := f n) (y := ⟨_, hdom⟩) rfl]
    exact FunctionalInequalities.Energy.WeightedGradient.operator_apply ν B hac (hν.frontier_support_eq_zero hi)
      (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)) hdom (hgeq n)
  refine ⟨g, hg, hgc, ?_, ?_⟩
  · have h1 : Tendsto (fun n => (f n : Lp ℝ 2 (ν : Measure V))) atTop
        (𝓝 (x : Lp ℝ 2 (ν : Measure V))) := by
      have h := (continuous_fst.tendsto ((x : Lp ℝ 2 (ν : Measure V)),
        hν.closedWeightedOperator m B hi x)).comp hf
      simpa [Function.comp_def] using h
    exact h1.congr fun n => hgeq n
  · have h2 : Tendsto
        (fun n => (hν.weightedOperator m B hi).domRestrict (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν) (f n)) atTop
        (𝓝 (hν.closedWeightedOperator m B hi x)) := by
      have h := (continuous_snd.tendsto ((x : Lp ℝ 2 (ν : Measure V)),
        hν.closedWeightedOperator m B hi x)).comp hf
      simpa [Function.comp_def] using h
    exact h2.congr fun n => hval n

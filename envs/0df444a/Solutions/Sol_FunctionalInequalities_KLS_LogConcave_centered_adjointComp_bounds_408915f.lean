-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.centered_adjointComp_bounds_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:50:55.998662+00:00
-- url     : https://prove2.me/submissions/5b087af2-20a1-44c8-9ce5-96c1b85fe2f3

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
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_le_of_gap_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_id_gap_of_literature_le_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_orthogonal_ker_iff_mean_eq_zero_408915f

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
/-- The zero constant is the zero element of `L²`. -/
@[simp]
theorem FunctionalInequalities.L2.const_zero (μ : ProbabilityMeasure α) : const μ 0 = 0 :=
  map_zero (Lp.const 2 (μ : Measure α))
end
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
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
open Analysis.Semigroup Analysis.Semigroup.Generated
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
include hνU hU in
/-- **BKL Lemma 2.1, operator-domain part (bounds (20) and (24)).** With `C ≥ C_P(ν) = λ⁻¹`, a
centered `u` in the generator domain with `A u = g` satisfies `‖u‖ ≤ C ‖g‖`,
`‖T̄ u‖² = ⟪g, u⟫ ≤ C ‖g‖²` and `‖T̄ u‖ ≤ √C ‖g‖`. -/
theorem solution {C : NNReal}
    (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (u : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hu : FunctionalInequalities.L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0) :
    ‖(u : Lp ℝ 2 (ν : Measure V))‖ ≤
        (C : ℝ) * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ^ 2 =
        ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
          (u : Lp ℝ 2 (ν : Measure V))⟫ ∧
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u,
          (u : Lp ℝ 2 (ν : Measure V))⟫ ≤
        (C : ℝ) * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ≤
        Real.sqrt C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ := by
    have hd :
        Dense
          ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :
            Set (Lp ℝ 2 (ν : Measure V))) :=
      hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    have hgap :
        ∀ y : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
          (∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
              hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
                ⟪(y : Lp ℝ 2 (ν : Measure V)),
                  (k : Lp ℝ 2 (ν : Measure V))⟫ = 0) →
            ‖(y : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
              (C : ℝ) *
                ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi y‖ ^ 2 := by
      intro y hy
      have hymean :
          FunctionalInequalities.L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 :=
        (FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_408915f m hν hi hνU hU
          (y : Lp ℝ 2 (ν : Measure V))).mp hy
      have hcenter :
          FunctionalInequalities.L2.center ν (y : Lp ℝ 2 (ν : Measure V)) =
            (y : Lp ℝ 2 (ν : Measure V)) := by
        simp [FunctionalInequalities.L2.center, hymean]
      have h :=
        hν.closedWeightedOperator_id_gap_of_literature_le_408915f m hi C hC y
      rw [hcenter] at h
      exact h
    have huorth :
        ∀ k : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
          hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi k = 0 →
            ⟪(u : Lp ℝ 2 (ν : Measure V)),
              (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 :=
      (FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_408915f m hν hi hνU hU
        (u : Lp ℝ 2 (ν : Measure V))).mpr hu
    obtain ⟨hu₁, hu₂, hu₃⟩ :=
      FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap_408915f
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) hd hgap u huorth
    refine ⟨hu₁, hu₂, hu₃, ?_⟩
    have hsq :
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ ^ 2 ≤
          (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 := by
      rw [hu₂]
      exact hu₃
    have hsqrt :
        (Real.sqrt (C : ℝ)) ^ 2 = (C : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt_nonneg : 0 ≤ Real.sqrt (C : ℝ) :=
      Real.sqrt_nonneg _
    have hnorm₁ :
        0 ≤
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ :=
      norm_nonneg _
    have hnorm₂ :
        0 ≤
          ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ :=
      norm_nonneg _
    by_contra hnot
    have hlt :
        Real.sqrt (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ <
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ :=
      lt_of_not_ge hnot
    have hprod :
        0 ≤
          Real.sqrt (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ :=
      mul_nonneg hsqrt_nonneg hnorm₂
    have hsum :
        0 <
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ +
            Real.sqrt (C : ℝ) *
              ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ := by
      linarith
    have hfac :
        0 <
          (‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ -
            Real.sqrt (C : ℝ) *
              ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) *
          (‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(u : Lp ℝ 2 (ν : Measure V)), u.2.2⟩‖ +
            Real.sqrt (C : ℝ) *
              ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) :=
      mul_pos (sub_pos.mpr hlt) hsum
    have hsq' :
        (Real.sqrt (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖) ^ 2 =
          (C : ℝ) *
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u‖ ^ 2 := by
      rw [mul_pow, hsqrt]
    nlinarith [hfac, hsq, hsq']

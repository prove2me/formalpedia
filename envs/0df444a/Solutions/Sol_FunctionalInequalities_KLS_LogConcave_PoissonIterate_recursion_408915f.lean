-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.recursion_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:46:15.623636+00:00
-- url     : https://prove2.me/submissions/3ec6318c-dd05-4edc-b902-4b9b18aac614

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
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
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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

noncomputable section
open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff
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
section Scalar
/-- Each index `j < M` lies in at most `L` of the windows `[k + 1 - L, k)`, `k < M`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_window_le {χ : ℕ → ℝ} (hχ : ∀ j, 0 ≤ χ j) (L M : ℕ) :
    ∑ k ∈ range M, ∑ j ∈ Ico (k + 1 - L) k, χ j ≤ L * ∑ j ∈ range M, χ j := by
  rw [Finset.sum_comm' (t' := range M)
    (s' := fun j => (range M).filter fun k => k + 1 - L ≤ j ∧ j < k)
    (fun k j => by simp only [mem_range, mem_Ico, mem_filter]; omega), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hχ j)
  have hsub : (range M).filter (fun k => k + 1 - L ≤ j ∧ j < k) ⊆ Ioc j (j + L) := by
    intro k hk
    simp only [mem_filter, mem_range, mem_Ioc] at hk ⊢
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc, Nat.add_sub_cancel_left] at hcard
  exact_mod_cast hcard
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
/-- **The recursion (63)** in the operator route. With `λ = 1/C`,
`S_d = Σ_{k < N - d} t_d(k)`, the Lemma 3.8 bound `hJ1` for `2d ≤ k + 1` and the crude bound
`t_d(k) ≤ R^{2d} v_{k+1} ≤ 1.21 λ R^{2d}` for the at most `2d` remaining indices give
`S_d ≤ (cλ)^d S_{2d} + 5 d c^d λ R^{2d}`. -/
 theorem solution {C c R : ℝ} {v χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ} {N d : ℕ}
    (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R) (hd : 1 ≤ d)
    (hvk : ∀ k, v (k + 1) ≤ 121 / 100 * C⁻¹)
    (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2)
    (hαN : ∀ j, j + 1 < N → 0 < α j ∧ α j ^ 2 ≤ 3 / C)
    (ht : ∀ d k, 0 ≤ t d k)
    (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
    (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
      t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
        c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j) :
    ∑ k ∈ range (N - d), t d k ≤
      (c / C) ^ d * ∑ k ∈ range (N - 2 * d), t (2 * d) k +
        5 * d * c ^ d * C⁻¹ * R ^ (2 * d) := by
  have hl : 0 < C⁻¹ := inv_pos.mpr hC
  have hcd : 1 ≤ c ^ d := one_le_pow₀ hc
  have hRd : 0 ≤ R ^ (2 * d) := by positivity
  set P : ℕ → Prop := fun k => 2 * d ≤ k + 1 with hP
  set W : ℕ → ℝ := fun k => ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j with hW
  have hW0 : ∀ k, 0 ≤ W k := fun k => Finset.sum_nonneg fun j _ => hχ j
  rw [← Finset.sum_filter_add_sum_filter_not (range (N - d)) P]
  -- the indices `k + 1 ≥ 2d`, where Lemma 3.8 applies
  have hA : ∑ k ∈ (range (N - d)).filter P, t d k ≤
      (c / C) ^ d * ∑ k ∈ range (N - 2 * d), t (2 * d) k +
        c ^ d * R ^ (2 * d) * C * (2 * d * (11 / 10 * C⁻¹) ^ 2) := by
    have h1 : ∑ k ∈ (range (N - d)).filter P, t d k ≤
        ∑ k ∈ (range (N - d)).filter P,
          ((c / C) ^ d * t (2 * d) (k - d) + c ^ d * R ^ (2 * d) * C * W k) := by
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [mem_filter, mem_range, hP] at hk
      exact hJ1 k d hd hk.2 fun j hj => hαN j (by omega)
    have h2 : ∑ k ∈ (range (N - d)).filter P, t (2 * d) (k - d) ≤
        ∑ k ∈ range (N - 2 * d), t (2 * d) k := by
      rw [← Finset.sum_image (g := fun k => k - d) (f := t (2 * d)) (fun x hx y hy hxy => by
        simp only [mem_filter, mem_range, hP, mem_coe] at hx hy
        simp only at hxy
        omega)]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => ht _ _
      simp only [mem_image, mem_filter, mem_range, hP] at hi ⊢
      omega
    have h3 : ∑ k ∈ (range (N - d)).filter P, W k ≤ 2 * d * (11 / 10 * C⁻¹) ^ 2 := by
      calc ∑ k ∈ (range (N - d)).filter P, W k ≤ ∑ k ∈ range (N - d), W k :=
            Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => hW0 k
        _ ≤ ((2 * d : ℕ) : ℝ) * ∑ j ∈ range (N - d), χ j := sum_window_le hχ _ _
        _ ≤ ((2 * d : ℕ) : ℝ) * L 0 := mul_le_mul_of_nonneg_left (hχsum _) (by positivity)
        _ ≤ ((2 * d : ℕ) : ℝ) * (11 / 10 * C⁻¹) ^ 2 :=
            mul_le_mul_of_nonneg_left hL0 (by positivity)
        _ = 2 * d * (11 / 10 * C⁻¹) ^ 2 := by push_cast; ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have hcC : 0 ≤ (c / C) ^ d := by positivity
    have hcR : 0 ≤ c ^ d * R ^ (2 * d) * C := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hcC, mul_le_mul_of_nonneg_left h3 hcR]
  -- the indices `k + 1 < 2d`, at most `2d` of them, each at most `1.21 λ R^{2d}`
  have hB : ∑ k ∈ (range (N - d)).filter (fun k => ¬ P k), t d k ≤
      2 * d * (R ^ (2 * d) * (121 / 100 * C⁻¹)) := by
    have hcard : (((range (N - d)).filter (fun k => ¬ P k)).card : ℝ) ≤ 2 * d := by
      have hsub : (range (N - d)).filter (fun k => ¬ P k) ⊆ range (2 * d) := by
        intro k hk
        simp only [mem_filter, mem_range, hP] at hk ⊢
        omega
      have := Finset.card_le_card hsub
      rw [card_range] at this
      exact_mod_cast this
    calc ∑ k ∈ (range (N - d)).filter (fun k => ¬ P k), t d k
        ≤ ((range (N - d)).filter (fun k => ¬ P k)).card • (R ^ (2 * d) * (121 / 100 * C⁻¹)) :=
          Finset.sum_le_card_nsmul _ _ _ fun k _ =>
            (htaylor d k hd).trans (mul_le_mul_of_nonneg_left (hvk k) hRd)
      _ ≤ 2 * d * (R ^ (2 * d) * (121 / 100 * C⁻¹)) := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hCl : C * (11 / 10 * C⁻¹) ^ 2 = 121 / 100 * C⁻¹ := by
    field_simp
    ring
  have hX : 0 ≤ d * R ^ (2 * d) * C⁻¹ := by positivity
  have hcX := mul_le_mul_of_nonneg_left hcd hX
  have hE : c ^ d * R ^ (2 * d) * C * (2 * d * (11 / 10 * C⁻¹) ^ 2) =
      242 / 100 * (c ^ d * (d * R ^ (2 * d) * C⁻¹)) := by
    rw [show c ^ d * R ^ (2 * d) * C * (2 * d * (11 / 10 * C⁻¹) ^ 2) =
      2 * d * c ^ d * R ^ (2 * d) * (C * (11 / 10 * C⁻¹) ^ 2) by ring, hCl]
    ring
  rw [hE] at hA
  nlinarith

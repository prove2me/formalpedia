-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_taylorField_grad0_iter_sq_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:56:24.884449+00:00
-- url     : https://prove2.me/submissions/bd0994d2-79bf-44a8-bd2f-61daa2827559

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_symmetrize_taylorField_grad0_step_408915f

section
noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- `fixingOutside` is monotone. -/
theorem FunctionalInequalities.Analysis.Tensor.fixingOutside_mono {s t : Finset Ω} (hst : s ⊆ t) : fixingOutside s ⊆ fixingOutside t := by
    intro σ hσ
    have hσ' : ∀ x, x ∉ s → σ x = x := by
      simpa [fixingOutside] using hσ
    have h : ∀ x, x ∉ t → σ x = x := by
      intro x hx
      apply hσ' x
      intro hxs
      exact hx (hst hxs)
    simpa [fixingOutside] using h
end
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
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
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
variable {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
include hνU hU hexp hC in
/-- **BKL Corollary 3.7** (52) along the iterates: for `d ≥ 1`,
`S_{d+1} T_d(∇₀h_{k+2}) = α_{k+2} T_{d+1}(∇₀h_{k+1})`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) {d : ℕ}
    (hd : 1 ≤ d) (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)) :
    symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
        (taylorField d (grad0 T̄ (iter T̄ f (k + 1)))) (J ∘ Fin.cast (by omega)) =
      scale T̄ (iter T̄ f k) * taylorField (d + 1) (grad0 T̄ (iter T̄ f k)) J :=
  symmetrize_taylorField_grad0_step_408915f m hν hi hνU hU hexp hC _ hd J
end HeatModel
end
end
end
end
end
end

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
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
section
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
section Block
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.one_mem_fixingOutside' (s : Finset Ω) :
    (1 : Equiv.Perm Ω) ∈ fixingOutside s := by
  simp [fixingOutside]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mul_mem_fixingOutside' {s : Finset Ω} {σ τ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) (hτ : τ ∈ fixingOutside s) : σ * τ ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ hτ ⊢
  intro x hx
  simp [Equiv.Perm.coe_mul, hσ x hx, hτ x hx]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_mem_fixingOutside' {s : Finset Ω} {σ : Equiv.Perm Ω}
    (hσ : σ ∈ fixingOutside s) : σ⁻¹ ∈ fixingOutside s := by
  simp only [fixingOutside, mem_filter, mem_univ, true_and] at hσ ⊢
  intro x hx
  have h := congrArg (fun y => σ⁻¹ y) (hσ x hx)
  simpa using h.symm
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_fixingOutside_mul_right {M : Type*} [AddCommMonoid M] {s : Finset Ω}
    {τ : Equiv.Perm Ω} (hτ : τ ∈ fixingOutside s) (g : Equiv.Perm Ω → M) :
    ∑ σ ∈ fixingOutside s, g (σ * τ) = ∑ σ ∈ fixingOutside s, g σ :=
  sum_nbij' (· * τ) (· * τ⁻¹) (fun _ hσ => mul_mem_fixingOutside' hσ hτ)
    (fun _ hσ => mul_mem_fixingOutside' hσ (inv_mem_fixingOutside' hτ))
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => rfl)
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.card_fixingOutside_pos (s : Finset Ω) : (0 : ℝ) < (fixingOutside s).card := by
  exact_mod_cast card_pos.mpr ⟨1, one_mem_fixingOutside' s⟩
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_blockAverage_le (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (v : W) :
    ‖blockAverage ρ s v‖ ≤ ‖v‖ := by
  have hG := card_fixingOutside_pos s
  rw [blockAverage, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hG)]
  calc ((fixingOutside s).card : ℝ)⁻¹ * ‖∑ σ ∈ fixingOutside s, ρ σ v‖
      ≤ ((fixingOutside s).card : ℝ)⁻¹ * ∑ σ ∈ fixingOutside s, ‖ρ σ v‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hG.le)
    _ = ‖v‖ := by
        simp only [LinearIsometryEquiv.norm_map, sum_const, nsmul_eq_mul]
        rw [inv_mul_cancel_left₀ hG.ne']
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.blockAverage_smul (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) (s : Finset Ω) (c : ℝ)
    (v : W) : blockAverage ρ s (c • v) = c • blockAverage ρ s v := by
  simp only [blockAverage, map_smul, ← smul_sum, smul_comm c]
/-- Averaging over a group absorbs the average over a subgroup. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.blockAverage_blockAverage (ρ : Equiv.Perm Ω →* (W ≃ₗᵢ[ℝ] W)) {s t : Finset Ω}
    (hst : s ⊆ t) (v : W) : blockAverage ρ t (blockAverage ρ s v) = blockAverage ρ t v := by
  have hG := card_fixingOutside_pos s
  have hmul : ∀ σ τ : Equiv.Perm Ω, ρ σ (ρ τ v) = ρ (σ * τ) v := fun σ τ => by
    rw [map_mul]
    rfl
  simp only [blockAverage, map_smul, map_sum, hmul]
  congr 1
  rw [← smul_sum, sum_comm]
  have h : ∀ τ ∈ fixingOutside s,
      ∑ σ ∈ fixingOutside t, ρ (σ * τ) v = ∑ σ ∈ fixingOutside t, ρ σ v := fun τ hτ =>
    sum_fixingOutside_mul_right (fixingOutside_mono hst hτ) (fun σ => ρ σ v)
  rw [sum_congr rfl h, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ hG.ne']
end Block
section Coordinates
variable {n N : ℕ}
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.slots_zero_subset {q q' : ℕ} (h : q ≤ q') : slots N 0 q ⊆ slots N 0 q' := by
  intro x hx
  simp only [slots, mem_filter, mem_univ, true_and] at hx ⊢
  omega
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_le (q : ℕ) (A : Coord n N) : ‖symmetrize n N q A‖ ≤ ‖A‖ :=
  norm_blockAverage_le _ _ _
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_smul (q : ℕ) (c : ℝ) (A : Coord n N) :
    symmetrize n N q (c • A) = c • symmetrize n N q A :=
  blockAverage_smul _ _ _ _
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_symmetrize {q q' : ℕ} (h : q ≤ q') (A : Coord n N) :
    symmetrize n N q' (symmetrize n N q A) = symmetrize n N q' A :=
  blockAverage_blockAverage _ (slots_zero_subset h) A
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast_rfl (A : Coord n N) : FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast rfl A = A := by
  ext J
  simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_recast {N' : ℕ} (h : N = N') (A : Coord n N) : ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast h A‖ = ‖A‖ := by
  subst h
  rw [recast_rfl]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_recast {N' : ℕ} (h : N = N') (q : ℕ) (A : Coord n N) :
    symmetrize n N' q (FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast h A) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast h (symmetrize n N q A) := by
  subst h
  rw [recast_rfl, recast_rfl]
end Coordinates
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two' (hUt : U.HasTemperateGrowth) : ContDiff ℝ 2 U :=
  hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
include hνU hUt hexp hC in
/-- **BKL (56)–(57)**: iterating Corollary 3.7. If `α_{j+2}² ≤ β/C` for `j < k`, `e ≤ k` and
`d ≥ 1`, then `|S_{d+e} T_d(∇₀h_{k+1})|² ≤ (β/C)^e |T_{d+e}(∇₀h_{k+1-e})|²`. -/
theorem solution (f : Lp ℝ 2 (ν : Measure V)) {β : ℝ}
    (e : ℕ) : ∀ (d k : ℕ), 1 ≤ d → e ≤ k → (∀ j < k, FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j) ^ 2 ≤ β / C) →
      ‖FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + (k + 1)) (d + e)
          (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)))‖ ^ 2 ≤
        (β / C) ^ e * ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + e) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - e)))‖ ^ 2 := by
  induction e with
  | zero =>
    intro d k _ _ _
    rw [pow_zero, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_symmetrize_le _ _) 2
  | succ e ih =>
    intro d k hd hk hβ
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show d + (e + 1) = d + 1 + e by omega, show k + 1 - (e + 1) = k - e by omega]
    have hN : d + (k + 1 + 1) = d + 1 + (k + 1) := by omega
    have hS2 : FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast hN (FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + (k + 1 + 1)) (d + 1)
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k + 1))))) =
        FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k) • FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)) := by
      ext J
      simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.recast, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
      exact FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_iter_succ m hν hi hνU (contDiff_two' hUt) hexp hC f k
        hd J
    have hnorm : ‖FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + (k + 1 + 1)) (d + 1 + e)
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k + 1))))‖ =
        |FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)| * ‖FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + 1 + (k + 1)) (d + 1 + e)
          (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)))‖ := by
      rw [← symmetrize_symmetrize (q := d + 1) (by omega), ← norm_recast hN,
        ← symmetrize_recast, hS2, symmetrize_smul, norm_smul, Real.norm_eq_abs]
    have hα := hβ k (by omega)
    have hβC : 0 ≤ β / C := (sq_nonneg _).trans hα
    have ih' := ih (d + 1) k (by omega) (by omega) fun j hj => hβ j (by omega)
    rw [hnorm, mul_pow, sq_abs, pow_succ]
    calc FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k) ^ 2 * ‖FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + 1 + (k + 1))
          (d + 1 + e) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)))‖ ^ 2
        ≤ β / C * ((β / C) ^ e *
            ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1 + e) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - e)))‖ ^ 2) :=
          mul_le_mul hα ih' (sq_nonneg _) hβC
      _ = _ := by ring

-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_le_of_adjacent_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:51:16.677421+00:00
-- url     : https://prove2.me/submissions/05a87e52-5e94-4cba-9188-47244c4130ce

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
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

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Tensor
open scoped Classical
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : ProbabilityMeasure V} {k : ℕ}
/-- `permField` is a left action: `permField (σ * τ) = permField σ ∘ permField τ`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_mul (σ τ : Equiv.Perm (Fin k)) (u : Field ν k) :
    permField (σ * τ) u = permField σ (permField τ u) := rfl
/-- `permField σ` commutes with subtraction. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_sub (σ : Equiv.Perm (Fin k)) (u v : Field ν k) :
    permField σ (u - v) = permField σ u - permField σ v := rfl
/-- `normSq u` is the squared norm of `u` in `PiLp 2`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_eq_norm_toLp_sq (u : Field ν k) :
    normSq u = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl
/-- The Hilbert–Schmidt norm `√(normSq u)` is the norm of `u` in `PiLp 2`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_eq (u : Field ν k) :
    √(normSq u) = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ := by
  rw [normSq_eq_norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]
/-- The triangle inequality for the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_add_le (u v : Field ν k) :
    √(normSq (u + v)) ≤ √(normSq u) + √(normSq v) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_add]
  exact norm_add_le _ _
/-- `normSq` is invariant under negation. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_neg (u : Field ν k) : normSq (-u) = normSq u := by
  simp [normSq]
/-- `permField σ` preserves the squared Hilbert–Schmidt norm. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_permField (σ : Equiv.Perm (Fin k)) (u : Field ν k) :
    normSq (permField σ u) = normSq u := by
  unfold normSq
  exact (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (Module.finrank ℝ V)))).sum_comp
    fun J => ‖u J‖ ^ 2
/-- Subadditivity of the displacement: `d(σ τ) ≤ d(σ) + d(τ)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_mul_le (σ τ : Equiv.Perm (Fin k)) (u : Field ν k) :
    √(normSq (u - permField (σ * τ) u)) ≤
      √(normSq (u - permField σ u)) + √(normSq (u - permField τ u)) := by
  have h : u - permField (σ * τ) u = (u - permField σ u) + permField σ (u - permField τ u) := by
    rw [permField_sub, permField_mul]
    abel
  rw [h]
  refine (sqrt_normSq_add_le _ _).trans ?_
  rw [normSq_permField]
/-- The displacement of `σ⁻¹` equals that of `σ`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_permField_inv (σ : Equiv.Perm (Fin k)) (u : Field ν k) :
    normSq (u - permField σ⁻¹ u) = normSq (u - permField σ u) := by
  have h : u - permField σ⁻¹ u = -permField σ⁻¹ (u - permField σ u) := by
    rw [permField_sub, ← permField_mul, inv_mul_cancel, permField_one]
    abel
  rw [h, normSq_neg, normSq_permField]
/-- Membership in the permutations of the first `p` positions. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero {p : ℕ} {σ : Equiv.Perm (Fin k)} :
    σ ∈ fixingOutside (slots k 0 p) ↔ ∀ x : Fin k, p ≤ x.val → σ x = x := by
  simp only [fixingOutside, slots, mem_filter, mem_univ, true_and, zero_le, not_lt]
/-- `finRotate k ℓ = ℓ + 1` below the last position. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.val_finRotate_of_lt {ℓ : Fin k} (h : ℓ.val + 1 < k) :
    (finRotate k ℓ).val = ℓ.val + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have := finRotate_of_lt (n := m) (k := ℓ.val) (by omega)
  rw [show ℓ = ⟨ℓ.val, ℓ.val.lt_succ_of_lt (by omega)⟩ from rfl, this]
/-- A chain of adjacent transpositions moving position `a` up to position `b`: some
permutation of the first `b + 1` positions sends `a` to `b` with displacement at most
`(b - a) B`, if every adjacent transposition `τ_ℓ` with `ℓ + 1 < q` has displacement at most
`B`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_chain {q : ℕ} (u : Field ν k) {B : ℝ}
    (hB : ∀ ℓ : Fin k, ℓ.val + 1 < q →
      √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤ B) :
    ∀ (n : ℕ) (a b : Fin k), b.val = a.val + n → b.val < q →
      ∃ ρ ∈ fixingOutside (slots k 0 (b.val + 1)), ρ a = b ∧
        √(normSq (u - permField ρ u)) ≤ n * B := by
  intro n
  induction n with
  | zero =>
    intro a b hab _
    have : b = a := Fin.ext (by simpa using hab)
    subst this
    refine ⟨1, mem_fixingOutside_slots_zero.mpr fun _ _ => rfl, rfl, ?_⟩
    simp [normSq]
  | succ n ih =>
    intro a b hab hbq
    set b' : Fin k := ⟨b.val - 1, by omega⟩ with hb'
    obtain ⟨ρ', hρ'mem, hρ'a, hρ'd⟩ := ih a b' (by simp [hb']; omega) (by simp [hb']; omega)
    have hrot : finRotate k b' = b := Fin.ext (by
      rw [val_finRotate_of_lt (by simp [hb']; omega)]; simp [hb']; omega)
    refine ⟨Equiv.swap b' b * ρ', ?_, ?_, ?_⟩
    · rw [mem_fixingOutside_slots_zero] at hρ'mem ⊢
      intro x hx
      have hxb' : x ≠ b' := fun h => by subst h; simp [hb'] at hx; omega
      have hxb : x ≠ b := fun h => by subst h; omega
      rw [Equiv.Perm.mul_apply, hρ'mem x (by simp [hb'] at hx ⊢; omega),
        Equiv.swap_apply_of_ne_of_ne hxb' hxb]
    · rw [Equiv.Perm.mul_apply, hρ'a, Equiv.swap_apply_left]
    · refine (sqrt_normSq_sub_permField_mul_le _ _ u).trans ?_
      have h1 := hB b' (by simp [hb']; omega)
      rw [hrot] at h1
      push_cast
      linarith
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
/-- **Word length bound for the displacement.** If every adjacent transposition `τ_ℓ`
(`ℓ + 1 < q`) moves `u` by at most `B` in the Hilbert–Schmidt norm, then every permutation of
the first `q` positions moves `u` by at most `q² B`. -/
theorem solution {q : ℕ} (hq : q ≤ k) (u : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ ℓ : Fin k, ℓ.val + 1 < q →
      √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤ B)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 q)) :
    √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField σ u)) ≤ (q : ℝ) ^ 2 * B := by
  suffices ∀ p ≤ q, ∀ σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 p),
      √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField σ u)) ≤ (p : ℝ) ^ 2 * B from this q le_rfl σ hσ
  intro p
  induction p with
  | zero =>
    intro _ σ hσ
    have : σ = 1 := Equiv.ext fun x => FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero.mp hσ x (Nat.zero_le _)
    subst this
    simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq]
  | succ p ih =>
    intro hpq σ hσ
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero] at hσ
    set b : Fin k := ⟨p, by omega⟩ with hb
    have hbv : b.val = p := rfl
    have ha : (σ b).val ≤ p := by
      by_contra h
      have hfix := hσ (σ b) (by omega)
      have : σ b = b := σ.injective hfix
      rw [this] at h
      simp [hb] at h
    obtain ⟨ρ, hρmem, hρa, hρd⟩ :=
      exists_chain u hB (p - (σ b).val) (σ b) b (by rw [hbv]; omega) (by rw [hbv]; omega)
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero] at hρmem
    have hσ' : ρ * σ ∈ FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 p) := by
      rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero]
      intro x hx
      rcases eq_or_ne x b with rfl | hxb
      · rw [Equiv.Perm.mul_apply, hρa]
      · have hx' : p + 1 ≤ x.val := by
          have : x.val ≠ p := fun h => hxb (Fin.ext (by simp [hb, h]))
          omega
        rw [Equiv.Perm.mul_apply, hσ x hx', hρmem x (by simp [hb]; omega)]
    have hdecomp : σ = ρ⁻¹ * (ρ * σ) := by group
    have h1 := FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_mul_le ρ⁻¹ (ρ * σ) u
    rw [← hdecomp, FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_permField_inv] at h1
    have h2 := ih (by omega) _ hσ'
    have h3 : ((p - (σ b).val : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le _ _
    have h4 : ((p - (σ b).val : ℕ) : ℝ) * B ≤ p * B := mul_le_mul_of_nonneg_right h3 hB0
    have h5 : (p : ℝ) * B + (p : ℝ) ^ 2 * B ≤ ((p + 1 : ℕ) : ℝ) ^ 2 * B := by
      push_cast
      nlinarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    linarith

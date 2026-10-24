-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_symField_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:53:15.133665+00:00
-- url     : https://prove2.me/submissions/378e3d8b-dd6b-4a0a-a93e-4a8b4d4513c5

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_sqrt_normSq_sub_permField_le_of_adjacent_408915f

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `normSq` is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ normSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
end
end
end
end
end
end

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
/-- Homogeneity of the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_smul (c : ℝ) (u : Field ν k) :
    √(normSq (c • u)) = |c| * √(normSq u) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
/-- The triangle inequality for finite sums in the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Field ν k) :
    √(normSq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(normSq (f i)) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_sum]
  exact norm_sum_le _ _
/-- Membership in the permutations of the first `p` positions. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero {p : ℕ} {σ : Equiv.Perm (Fin k)} :
    σ ∈ fixingOutside (slots k 0 p) ↔ ∀ x : Fin k, p ≤ x.val → σ x = x := by
  simp only [fixingOutside, slots, mem_filter, mem_univ, true_and, zero_le, not_lt]
/-- The sum `Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²` dominates each of its terms' square roots. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_adjacent_le {q : ℕ} (u : Field ν k) (ℓ : Fin k) (hℓ : ℓ.val + 1 < q) :
    √(normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u)) ≤
      √(∑ m ∈ univ.filter (fun m : Fin k => m.val + 1 < q),
        normSq (u - permField (Equiv.swap m (finRotate k m)) u)) :=
  Real.sqrt_le_sqrt <| single_le_sum (f := fun m : Fin k =>
      normSq (u - permField (Equiv.swap m (finRotate k m)) u))
    (fun _ _ => normSq_nonneg _) (by simp [hℓ])
/-- `u - S_q u` is the average of the displacements `u - π u` over the permutations `π` of the
first `q` positions. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sub_symField_eq (q : ℕ) (u : Field ν k) :
    u - symField q u = ((fixingOutside (slots k 0 q)).card : ℝ)⁻¹ •
      ∑ σ ∈ fixingOutside (slots k 0 q), (u - permField σ u) := by
  have hne : ((fixingOutside (slots k 0 q)).card : ℝ) ≠ 0 := by
    have : (1 : Equiv.Perm (Fin k)) ∈ fixingOutside (slots k 0 q) :=
      mem_fixingOutside_slots_zero.mpr fun _ _ => rfl
    exact_mod_cast (card_pos.mpr ⟨1, this⟩).ne'
  rw [sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, inv_smul_smul₀ hne]
  rfl
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
/-- **BKL Lemma 3.3, (44).** For `q ≤ k` and a tensor field `u` with `k` indices,
`‖u - S_q u‖² ≤ q⁴ Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²`, where `S_q` averages over the permutations of the
first `q` index positions and `τ_ℓ` swaps positions `ℓ` and `ℓ + 1`. -/
theorem solution {q : ℕ} (hq : q ≤ k) (u : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.symField q u) ≤
      (q : ℝ) ^ 4 * ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
        FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ (finRotate k ℓ)) u) := by
  set S := ∑ ℓ ∈ univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ (finRotate k ℓ)) u)
  set G := FunctionalInequalities.Analysis.Tensor.fixingOutside (FunctionalInequalities.Analysis.Tensor.slots k 0 q)
  have hS : 0 ≤ S := sum_nonneg fun _ _ => FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg _
  have hG : (0 : ℝ) < G.card := by
    have : (1 : Equiv.Perm (Fin k)) ∈ G := FunctionalInequalities.KLS.LogConcave.PoissonIterate.mem_fixingOutside_slots_zero.mpr fun _ _ => rfl
    exact_mod_cast card_pos.mpr ⟨1, this⟩
  have hbound : √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.symField q u)) ≤ (q : ℝ) ^ 2 * √S := by
    rw [sub_symField_eq, FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_smul, abs_of_pos (inv_pos.mpr hG)]
    calc (G.card : ℝ)⁻¹ * √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (∑ σ ∈ G, (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField σ u)))
        ≤ (G.card : ℝ)⁻¹ * ∑ σ ∈ G, √(FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (u - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField σ u)) :=
          mul_le_mul_of_nonneg_left (FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sum_le _ _) (inv_nonneg.mpr hG.le)
      _ ≤ (G.card : ℝ)⁻¹ * ∑ _σ ∈ G, (q : ℝ) ^ 2 * √S := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun σ hσ => ?_) (inv_nonneg.mpr hG.le)
          exact FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_le_of_adjacent_408915f hq u (Real.sqrt_nonneg S)
            (fun ℓ hℓ => sqrt_normSq_adjacent_le u ℓ hℓ) hσ
      _ = (q : ℝ) ^ 2 * √S := by
          rw [sum_const, nsmul_eq_mul, inv_mul_cancel_left₀ hG.ne']
  have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2
  rw [Real.sq_sqrt (FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg _), mul_pow, Real.sq_sqrt hS, ← pow_mul] at h'
  exact h'

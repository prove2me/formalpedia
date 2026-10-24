-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_regular_moment_bounded_weak_hessian_testing_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:05:34.11968+00:00
-- url     : https://prove2.me/submissions/9b339512-11cc-411d-9267-3a21609470ab

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_compact_mul_data_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_hessian_evolution_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_memLp_mul_of_hasCompactSupport_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
private lemma FunctionalInequalities.Probability.Stein.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Probability.Stein.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
private lemma FunctionalInequalities.Probability.Stein.n11b_continuous_hessian_entry {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        FunctionalInequalities.Probability.Stein.n10_matrix L i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n11b_continuous_hessian_entry i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
end
end
end
end HessianEntryBounds
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
/-- The total coordinate Hessian entry is L2 on every compact set, from the
actual Lipschitz-gradient bound. No differentiability or PDE premise is added. -/
theorem FunctionalInequalities.Probability.Stein.memLp_hessianMatrix_entry_of_isCompact {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S) :
    MemLp (fun x => hessianMatrix u x i j) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact MemLp.of_bound
    (measurable_hessianMatrix_entry u i j).aestronglyMeasurable
    (G : ℝ)
    (Filter.Eventually.of_forall fun x =>
      norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x i j)
end
end
end
end
end

section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
section RegularMomentWeakHessianEvolution
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- Compact-local essential boundedness of the total Hessian entry, reusing its
canonical measurability and Lipschitz-gradient pointwise bound. -/
private theorem FunctionalInequalities.Analysis.memLp_top_hessianMatrix_entry_of_isCompact {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hGradLip : LipschitzWith G (gradient u)) (i j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => hessianMatrix u x i j) (⊤ : ENNReal)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact MemLp.of_bound
    (measurable_hessianMatrix_entry u i j).aestronglyMeasurable (G : ℝ)
    (Filter.Eventually.of_forall fun x => norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hGradLip x i j)
/-- Actual compact Hessian multipliers have the bounded H1 data; no global T2 is used. -/
private theorem FunctionalInequalities.Analysis.bounded_compact_hessian_test_data {n : ℕ}
    {u ψ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i j : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasCompactSupport (fun x => ψ x * hessianMatrix u x i j) ∧
      (∀ x, ‖ψ x * hessianMatrix u x i j‖ ≤ C) ∧
      MemLp (fun x => ψ x * hessianMatrix u x i j) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => ψ x * hessianMatrix u x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong (fun x => ψ x * hessianMatrix u x i j)
          (fun x => ψ x * T x k i j + fderiv ℝ ψ x
            (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (fun x => ψ x * T x k i j + fderiv ℝ ψ x
          (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x i j) ∧
        MemLp (fun x => ψ x * T x k i j + fderiv ℝ ψ x
          (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x i j) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨Cψ, hCψ⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hη2 : MemLp (fun x => ψ x * hessianMatrix u x i j) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_mul_of_hasCompactSupport_408915f hψ.continuous hψc
      (fun S hS => memLp_hessianMatrix_entry_of_isCompact hG i j hS)
  refine ⟨max Cψ 0 * (G : ℝ), mul_nonneg (le_max_right _ _) G.coe_nonneg,
    hψc.mul_right, ?_, hη2, hη2.locallyIntegrable one_le_two, ?_⟩
  · intro x
    rw [norm_mul]
    exact mul_le_mul ((hCψ x).trans (le_max_left _ _))
      (norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f hG x i j)
      (norm_nonneg _) (le_max_right _ _)
  · intro k
    have hdata := HasWeakDerivAlong.compact_mul_data_408915f (hT k i j).1 (hT k i j).2
      (fun S hS => memLp_top_hessianMatrix_entry_of_isCompact hG i j S hS) hψ hψc
    exact ⟨hdata.1, hdata.2.2.1, hdata.2.2.2⟩
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- The regular-class weighted Hessian evolution at the same witness, together with its bounded test
extension to `ψ * H_lk` for every compactly supported C1 `ψ`: both sides are integrable and the weighted
identity holds. No global L2 bound of `T` and no new source premise is used. -/
theorem solution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
        Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det *
            ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det)
          (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j)
          (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, FunctionalInequalities.Probability.Stein.hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong
        (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
                ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∀ b : Fin n, Integrable (fun x => Real.exp (-u x) * J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * (ψ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * (ψ x * T x b l k + fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b) * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * (ψ x * FunctionalInequalities.Probability.Stein.hessianMatrix u x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv, hmean, hq, hflux, hweighted⟩ :=
    FunctionalInequalities.Analysis.exists_regular_moment_weak_hessian_evolution_408915f hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
    filter_upwards [hd] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  refine ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, he, hfirst, hInv, hmean, hq, hflux, hweighted, ?_⟩
  dsimp only
  intro ψ hψ hψc l k i j
  obtain ⟨C, _hC, hηc, hbound, _hη2, hη, hweak⟩ :=
    bounded_compact_hessian_test_data hG T hT hψ hψc l k
  exact FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test_408915f hC1 hl hG
    (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv
    (fun b => (hfirst b).2.2.2.2) hη hbound hηc
    (fun b => (hweak b).1) (fun b => (hweak b).2.1) (fun b => (hweak b).2.2) i j

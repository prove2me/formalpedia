-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:44:25.609191+00:00
-- url     : https://prove2.me/submissions/1100623a-9557-4a77-8613-e7a77c04ca9e

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
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
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_integral_exp_neg_hessian_flux_eq_curvature_gram_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_flux_eq_neg_forcing_of_bounded_weak_test_408915f

noncomputable section
section BoundedWeightedHessianTesting
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
private theorem FunctionalInequalities.Analysis.compact_local_memLp_two_continuous_mul {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hχ : Continuous χ) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => χ x * f x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro S hS
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hχ.continuousOn
  have htop : MemLp χ (⊤ : ENNReal)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_top_of_bound hχ.measurable.aestronglyMeasurable.restrict C
      (ae_restrict_of_forall_mem hS.measurableSet hC)
  exact (hf S hS).mul' htop
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The weighted weak Hessian evolution identity extended to a bounded compactly supported test `η` whose
coordinate weak derivatives are compactly supported and globally L2, with both sides integrable. -/
theorem solution {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
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
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst : ∀ i : Fin n,
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ b : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong η (a b) (EuclideanSpace.basisFun (Fin n) ℝ b))
    (hac : ∀ b : Fin n, HasCompactSupport (a b))
    (ha2 : ∀ b : Fin n, MemLp (a b) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ b : Fin n, Integrable
        (fun x => Real.exp (-u x) * J x i j b * a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * a b x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * η x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
  let J := fun x i j b => ∑ c : Fin n, R x c b * T x c i j
  let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
    (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
    (R x * (Matrix.of fun b c => T x i b c) * R x *
      (Matrix.of fun b c => T x j b c)).trace
  let wgt := fun x => Real.exp (-u x)
  have hdata := FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_408915f
    hu hL hG hW hF hdet T hT hInv hFirst
  change ∀ i j : Fin n, _
  intro i j
  have hwgt : Continuous wgt := Real.continuous_exp.comp hu.continuous.neg
  have hJw (b : Fin n) : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => wgt x * J x i j b) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    compact_local_memLp_two_continuous_mul ((hdata i j).1 b) hwgt
  have hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ b : Fin n, (wgt x * J x i j b) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, (wgt x * E x i j) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro ψ hψ hψc
    calc
      _ = ∫ x, wgt x * (∑ b : Fin n, J x i j b *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          simp only [wgt, J, R, Finset.mul_sum, Finset.sum_mul, mul_assoc])
      _ = _ := (hdata i j).2.2.2 ψ hψ hψc
  have ht := FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test_408915f
    hJw (hdata i j).2.2.1 hId hη hbound hηc hweak hac ha2
  refine ⟨ht.1, ht.2.1, ?_⟩
  calc
    _ = ∫ x, ∑ b : Fin n, (wgt x * J x i j b) * a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [wgt, J, R, Finset.mul_sum, Finset.sum_mul, mul_assoc])
    _ = _ := ht.2.2

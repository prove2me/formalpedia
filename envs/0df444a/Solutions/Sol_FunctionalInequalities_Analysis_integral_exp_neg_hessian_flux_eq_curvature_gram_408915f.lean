-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:42:24.248298+00:00
-- url     : https://prove2.me/submissions/9ec68cac-41ab-4707-8cfc-1ae26e029a27

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
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_congr_ae_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_ae_hessian_flux_forcing_minus_drift_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_mongeAmpere_first_rhs_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_exp_neg_flux_of_unweighted_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_weak_hessian_flux_eq_trace_derivative_408915f

noncomputable section
section WeightedWeakHessianEvolution
open Matrix MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff
open scoped BigOperators
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 1200000 in
/-- Weighted weak Hessian evolution (weak Letwin (2.6)): the flux `J` is compact-local L2, the curvature
and Gram forcing `E = -H + H ∇²W(∇u) H + tr(H⁻¹Tᵢ H⁻¹Tⱼ)` and `e^{-u} E` are locally integrable, and
`∫ e^{-u} Σₐ Jᵢⱼₐ ∂ₐψ = -∫ e^{-u} Eᵢⱼ ψ` for every compactly supported C1 `ψ`. -/
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
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j))
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst : ∀ i : Fin n,
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) :
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
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
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  dsimp only
  intro i j
  let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
  let D := fun x k b a =>
    -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
  let Q := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i + ∑ a : Fin n,
    (T x j i a * fderiv ℝ W (gradient u x)
        (EuclideanSpace.basisFun (Fin n) ℝ a) +
      FunctionalInequalities.Probability.Stein.hessianMatrix u x i a * ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
        FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
  let C := fun x i j => Q x i j -
    (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
  let E := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
    (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
  have hQall :
      ∀ i j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong
            (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
              (Matrix.of fun a b => T x i a b)).trace)
            (fun x => Q x i j)
            (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => Q x i j) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro i j
    obtain ⟨hweak, hlocal⟩ :=
      FunctionalInequalities.Analysis.hasWeakDerivAlong_mongeAmpere_first_rhs_408915f hu hL hG hW T hT i j
    have htrace :
        (fun x =>
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
            ∑ a : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x i a *
              fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a)) =ᵐ[volume]
        (fun x =>
          ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x i a b)).trace) := by
      filter_upwards [hFirst i] with x hx
      exact hx.symm
    refine ⟨?_, ?_⟩
    · simpa only [Q] using
        hweak.congr_ae_408915f htrace (Filter.Eventually.of_forall fun _ => rfl)
    · simpa only [Q] using hlocal
  have hcf1 :=
    FunctionalInequalities.Analysis.integral_weak_hessian_flux_eq_trace_derivative_408915f hu hG T hT hInv Q hQall
  have hJmem :
      ∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    simpa only [J, R] using (hcf1 i j).1
  have hClocal :
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [C, D, Q, R] using (hcf1 i j).2.1
  have hJlocal (a : Fin n) :
      LocallyIntegrable (fun x => J x i j a)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [locallyIntegrable_iff]
    intro K hK
    have hfinite : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) := by
      rw [isFiniteMeasure_restrict]
      exact ne_of_lt hK.measure_lt_top
    exact @MemLp.integrable _ _ _ _ _ _ 2 (by norm_num) _
      hfinite (hJmem a K hK)
  have hdu (a : Fin n) :
      Continuous (fun x => fderiv ℝ u x
        (EuclideanSpace.basisFun (Fin n) ℝ a)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hJdu :
      LocallyIntegrable
        (fun x => ∑ a : Fin n, J x i j a *
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ
      (fun a _ => (hJlocal a).mul_continuous (hdu a))
  have hae :=
    FunctionalInequalities.Analysis.ae_hessian_flux_forcing_minus_drift_408915f hu hG hW hF hdet T hT hInv
  have hAE :
      (fun x =>
        C x i j -
          ∑ a : Fin n, J x i j a *
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =ᵐ[volume]
        (fun x => E x i j) := by
    filter_upwards [hae] with x hx
    simpa only [C, D, J, Q, E, R] using hx i j
  have hElocal :
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hClocal.sub hJdu).congr hAE
  have hweighted :=
    FunctionalInequalities.Analysis.integral_exp_neg_flux_of_unweighted_408915f hu hJlocal hClocal
      (fun φ hφ hφc => by
        simpa only [C, D, Q, R] using (hcf1 i j).2.2 φ hφ hφc)
  have hEweighted :
      LocallyIntegrable
        (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hweightedAE :
        (fun x => Real.exp (-u x) *
          (C x i j -
            ∑ a : Fin n, J x i j a *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a))) =ᵐ[volume]
          (fun x => Real.exp (-u x) * E x i j) := by
      filter_upwards [hAE] with x hx
      rw [hx]
    exact hweighted.1.congr hweightedAE
  have hfinal :
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) *
          (∑ a : Fin n, J x i j a *
            fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro ψ hψ hψc
    have hid := hweighted.2 ψ hψ hψc
    have hright :
        (fun x => Real.exp (-u x) *
          (C x i j -
            ∑ a : Fin n, J x i j a *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) * ψ x) =ᵐ[volume]
          (fun x => Real.exp (-u x) * E x i j * ψ x) := by
      filter_upwards [hAE] with x hx
      rw [hx]
    rw [integral_congr_ae hright] at hid
    exact hid
  exact ⟨hJmem, hElocal, hEweighted, hfinal⟩

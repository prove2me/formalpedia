-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_hessian_flux_forcing_minus_drift_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:38:43.054498+00:00
-- url     : https://prove2.me/submissions/49550346-3197-486a-b468-6efc2b7c03c3

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
import Theorems.Thm_FunctionalInequalities_Analysis_ae_fderiv_mongeAmpere_exponent_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_ae_inverse_hessian_row_divergence_of_weak_derivative_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_third_derivative_symm_408915f

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
section Hessian
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The bilinear second Fréchet derivative of a `C²` real-valued function is symmetric. -/
theorem FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w =
      bilinearIteratedFDerivTwo ℝ f x w v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons
end Hessian
end
end
end
end
end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section WeakThirdDerivativeSymmetry
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_symm_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    hessianMatrix u x i j = hessianMatrix u x j i := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hs :=
    second_derivative_symmetric
      (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
      hfd.hasFDerivAt
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using hs
end InnerProduct
end StructuredSpace
end
end
end WeakThirdDerivativeSymmetry
section GradientDerivativeIdentification
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
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
/-- The coordinate Hessian of a `C¹` potential is symmetric at every differentiability
point of its gradient, including the zero-dimensional case. -/
theorem FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    (hessianMatrix u x).IsHermitian := by
  change (hessianMatrix u x).conjTranspose = hessianMatrix u x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact hessian_symm_of_gradient_diff hu hx
end
end
end
end GradientDerivativeIdentification
end

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
/-- Closed scalar contraction form of the negative trace product. -/
private theorem FunctionalInequalities.Analysis.sum_entry_mul_neg_eq_neg_trace {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, B a b * (-(A b a))) = -(A * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_neg, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _
/-- The inverse-derivative contraction has the standard Gram trace order;
only trace cyclicity is used, never commutation of the matrices. -/
private theorem FunctionalInequalities.Analysis.sum_inverse_derivative_contraction_eq_neg_gram {n : ℕ}
    (R Ti Tj : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, Ti a b * (-((R * Tj * R) b a))) =
      -(R * Ti * R * Tj).trace := by
  rw [sum_entry_mul_neg_eq_neg_trace]
  have hCyclic : (R * Tj * R * Ti).trace = (R * Ti * R * Tj).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (R * Tj) (R * Ti)
  rw [hCyclic]
/-- The coordinate curvature expression before Hessian symmetry is applied. -/
private theorem FunctionalInequalities.Analysis.sum_curvature_eq_mul_transpose {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∑ a : Fin n, H i a * ∑ b : Fin n, H j b * A b a) =
      (H * Aᵀ * Hᵀ) i j := by
  rw [Matrix.mul_mul_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (fun t : ℝ => H i a * t)
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _
/-- The actual symmetric Hessian data identify the standard H A H entry. -/
private theorem FunctionalInequalities.Analysis.sum_curvature_eq_mul_of_symm {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ = H) (hA : Aᵀ = A)
    (i j : Fin n) :
    (∑ a : Fin n, H i a * ∑ b : Fin n, H j b * A b a) = (H * A * H) i j := by
  rw [sum_curvature_eq_mul_transpose, hH, hA]
/-- Row inverse/gradient cancellation in the Piola drift term. -/
private theorem FunctionalInequalities.Analysis.sum_row_mul_neg_add_hessian_eq {n : ℕ}
    (R H : Matrix (Fin n) (Fin n) ℝ) (hRH : R * H = 1)
    (v w : Fin n → ℝ) (b : Fin n) :
    (∑ a : Fin n, R b a * (-v a + ∑ c : Fin n, H a c * w c)) =
      -(∑ a : Fin n, R b a * v a) + w b := by
  have hVec : R.mulVec (-v + H.mulVec w) = -(R.mulVec v) + w := by
    rw [Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hRH, Matrix.one_mulVec]
  have hEntry := congrFun hVec b
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.neg_apply] using hEntry
/-- Closed row/trace algebra after the actual curl identity, before weighting. -/
private theorem FunctionalInequalities.Analysis.sum_weak_hessian_divergence_minus_drift_eq {n : ℕ}
    (R H A : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : Hᵀ = H) (hA : Aᵀ = A) (hRH : R * H = 1)
    (hT : ∀ k i j : Fin n, T k i j = T i k j ∧ T k i j = T k j i)
    (v w : Fin n → ℝ)
    (hrow : ∀ b : Fin n,
      (∑ a : Fin n, -((R * T a * R) b a)) =
        -(∑ a : Fin n, R b a * (-v a + ∑ c : Fin n, H a c * w c)))
    (i j : Fin n) :
    let D := fun k b a => -((R * T k * R) b a)
    let J := fun a => ∑ b : Fin n, R b a * T b i j
    let Q := -H j i + ∑ a : Fin n,
      (T j i a * w a + H i a * ∑ b : Fin n, H j b * A b a)
    Q - (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) +
        (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) -
        (∑ a : Fin n, J a * v a) =
      -H i j + (H * A * H) i j + (R * T i * R * T j).trace := by
  dsimp only
  let D := fun k b a => -((R * T k * R) b a)
  let J := fun a => ∑ b : Fin n, R b a * T b i j
  let Q := -H j i + ∑ a : Fin n,
    (T j i a * w a + H i a * ∑ b : Fin n, H j b * A b a)
  change Q - (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) +
      (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) -
      (∑ a : Fin n, J a * v a) = _
  have hHij : H j i = H i j := congrFun (congrFun hH i) j
  have hTperm (a : Fin n) : T j i a = T a i j :=
    (hT j i a).1.trans ((hT i j a).2.trans (hT i a j).1)
  have hQ : Q = -H i j + (H * A * H) i j + ∑ a : Fin n, T a i j * w a := by
    dsimp [Q]
    rw [Finset.sum_add_distrib, sum_curvature_eq_mul_of_symm H A hH hA i j, hHij]
    simp_rw [hTperm]
    ring
  have hGram : (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) =
      -(R * T i * R * T j).trace :=
    sum_inverse_derivative_contraction_eq_neg_gram R (T i) (T j)
  have hrow' (b : Fin n) : (∑ a : Fin n, D a b a) =
      (∑ a : Fin n, R b a * v a) - w b := by
    change (∑ a : Fin n, -((R * T a * R) b a)) = _
    rw [hrow b, sum_row_mul_neg_add_hessian_eq R H hRH v w b]
    ring
  have hRowTerm : (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) =
      (∑ b : Fin n, T b i j * (∑ a : Fin n, R b a * v a)) -
      (∑ b : Fin n, T b i j * w b) := by
    simp_rw [hrow']
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hcancel : (∑ b : Fin n, T b i j * (∑ a : Fin n, R b a * v a)) =
      ∑ a : Fin n, J a * v a := by
    simp only [J, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hQ, hGram, hRowTerm, hcancel]
  ring
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 1200000 in
 theorem solution {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u)
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
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let Q := fun x i j => -FunctionalInequalities.Probability.Stein.hessianMatrix u x j i + ∑ a : Fin n,
      (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
        FunctionalInequalities.Probability.Stein.hessianMatrix u x i a * ∑ b : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x j b *
          FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) b a)
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
      Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
        (∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)) -
        (∑ a : Fin n, J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =
      -FunctionalInequalities.Probability.Stein.hessianMatrix u x i j +
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x * FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) * FunctionalInequalities.Probability.Stein.hessianMatrix u x) i j +
        (R x * (Matrix.of fun a b => T x i a b) * R x *
          (Matrix.of fun a b => T x j a b)).trace := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
  let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  have hrow₀ := FunctionalInequalities.Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative_408915f hu hG hF hdet T hInv
  have hrows : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ b : Fin n, (∑ a : Fin n, D x a b a) =
        -(∑ a : Fin n, R x b a *
          fderiv ℝ (fun y => -u y + W (gradient u y)) x (e a)) :=
    ae_all_iff.mpr (fun b => (hrow₀ b).2)
  have hchain := FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_408915f hu hG (hW.of_le one_le_two)
  have hsymm := FunctionalInequalities.Analysis.ae_weak_third_derivative_symm_408915f hu hG (fun k i j => (hT k i j).1)
  filter_upwards [hrows, hchain, hsymm, hdet, hG.ae_differentiableAt (μ := volume)]
    with x hrow hc hs hd hx
  intro i j
  have hH : (FunctionalInequalities.Probability.Stein.hessianMatrix u x)ᵀ = FunctionalInequalities.Probability.Stein.hessianMatrix u x := by
    have hh := FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx
    ext a b
    simpa only [Matrix.transpose_apply, star_trivial] using hh.apply a b
  have hWsym : (FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x))ᵀ = FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x) := by
    ext a b
    exact FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm hW (gradient u x) (e b) (e a)
  have hRH : R x * FunctionalInequalities.Probability.Stein.hessianMatrix u x = 1 := by
    apply Matrix.nonsing_inv_mul
    apply isUnit_iff_ne_zero.mpr
    rw [hd]
    exact Real.exp_ne_zero _
  have hrow' (b : Fin n) : (∑ a : Fin n, D x a b a) =
      -(∑ a : Fin n, R x b a *
        (-fderiv ℝ u x (e a) + ∑ c : Fin n, FunctionalInequalities.Probability.Stein.hessianMatrix u x a c *
          fderiv ℝ W (gradient u x) (e c))) := by
    rw [hrow b]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [hc a]
  exact sum_weak_hessian_divergence_minus_drift_eq
    (R x) (FunctionalInequalities.Probability.Stein.hessianMatrix u x) (FunctionalInequalities.Probability.Stein.hessianMatrix W (gradient u x))
    (fun k => Matrix.of fun a b => T x k a b) hH hWsym hRH hs
    (fun a => fderiv ℝ u x (e a))
    (fun a => fderiv ℝ W (gradient u x) (e a)) hrow' i j

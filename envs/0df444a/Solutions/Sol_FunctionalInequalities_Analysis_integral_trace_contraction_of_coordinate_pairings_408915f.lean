-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_trace_contraction_of_coordinate_pairings_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:44:54.194605+00:00
-- url     : https://prove2.me/submissions/513fb5a7-9847-4828-b1d1-ea895dd9968f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_408915f

noncomputable section
section FixedTestFiniteContraction
open MeasureTheory Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private theorem FunctionalInequalities.Analysis.trace_quadratic_test_pair_contraction {n : ℕ}
    (B H J T : Matrix (Fin n) (Fin n) ℝ) (ψ dψ : ℝ) :
    (∑ q : Fin n × Fin n × Fin n × Fin n,
      (2 * (B q.1 q.2.1 * B q.2.2.1 q.2.2.2)) *
        (J q.2.2.2 q.1 * (ψ * T q.2.1 q.2.2.1 + dψ * H q.2.1 q.2.2.1))) =
    ψ * (2 * (B * T * B * J).trace) + dψ * (2 * (B * H * B * J).trace) := by
  rw [trace_mul_mul_mul_eq_sum_408915f, trace_mul_mul_mul_eq_sum_408915f]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring
private theorem FunctionalInequalities.Analysis.trace_quadratic_forcing_contraction {n : ℕ}
    (B H E : Matrix (Fin n) (Fin n) ℝ) (ψ : ℝ) :
    (∑ q : Fin n × Fin n × Fin n × Fin n,
      (2 * (B q.1 q.2.1 * B q.2.2.1 q.2.2.2)) *
        (E q.2.2.2 q.1 * (ψ * H q.2.1 q.2.2.1))) =
    ψ * (2 * (B * H * B * E).trace) := by
  rw [trace_mul_mul_mul_eq_sum_408915f]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 theorem solution {d n m : ℕ}
    (mu : Measure (EuclideanSpace ℝ (Fin d)))
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H E : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (T J : EuclideanSpace ℝ (Fin d) → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (rho psi : EuclideanSpace ℝ (Fin d) → ℝ)
    (dpsi : Fin m → EuclideanSpace ℝ (Fin d) → ℝ)
    (hPair : ∀ l k i j : Fin n, Integrable (fun x => rho x *
      (∑ a : Fin m, J x a i j * (psi x * T x a l k + dpsi a x * H x l k))) mu)
    (hForce : ∀ l k i j : Fin n, Integrable
      (fun x => rho x * E x i j * (psi x * H x l k)) mu)
    (hTensor : ∀ a : Fin m, Integrable
      (fun x => rho x * psi x * (2 * (B * T x a * B * J x a).trace)) mu)
    (hFlux : ∀ a : Fin m, Integrable
      (fun x => rho x * dpsi a x * (2 * (B * H x * B * J x a).trace)) mu)
    (hTraceForce : Integrable
      (fun x => rho x * psi x * (2 * (B * H x * B * E x).trace)) mu)
    (hTest : ∀ l k i j : Fin n,
      (∫ x, rho x * (∑ a : Fin m, J x a i j *
        (psi x * T x a l k + dpsi a x * H x l k)) ∂mu) =
      -(∫ x, rho x * E x i j * (psi x * H x l k) ∂mu)) :
    (∫ x, rho x * (∑ a : Fin m, (2 * (B * H x * B * J x a).trace) * dpsi a x) ∂mu) =
      -(∫ x, rho x *
        (2 * (B * H x * B * E x).trace +
          ∑ a : Fin m, 2 * (B * T x a * B * J x a).trace) * psi x ∂mu) := by
  classical
  let Q := Fin n × Fin n × Fin n × Fin n
  let c : Q → ℝ := fun q => 2 * (B q.1 q.2.1 * B q.2.2.1 q.2.2.2)
  let P : Q → EuclideanSpace ℝ (Fin d) → ℝ := fun q x =>
    rho x * ∑ a : Fin m, J x a q.2.2.2 q.1 *
      (psi x * T x a q.2.1 q.2.2.1 + dpsi a x * H x q.2.1 q.2.2.1)
  let F : Q → EuclideanSpace ℝ (Fin d) → ℝ := fun q x =>
    rho x * E x q.2.2.2 q.1 * (psi x * H x q.2.1 q.2.2.1)
  let A : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    ∑ a : Fin m, rho x * psi x * (2 * (B * T x a * B * J x a).trace)
  let C : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    ∑ a : Fin m, rho x * dpsi a x * (2 * (B * H x * B * J x a).trace)
  let K : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    rho x * psi x * (2 * (B * H x * B * E x).trace)
  have hP (q : Q) : Integrable (P q) mu :=
    hPair q.2.1 q.2.2.1 q.2.2.2 q.1
  have hF (q : Q) : Integrable (F q) mu :=
    hForce q.2.1 q.2.2.1 q.2.2.2 q.1
  have hPC (x) : (∑ q : Q, c q * P q x) = A x + C x := by
    calc
      _ = ∑ q : Q, ∑ a : Fin m, rho x * (c q *
          (J x a q.2.2.2 q.1 *
            (psi x * T x a q.2.1 q.2.2.1 + dpsi a x * H x q.2.1 q.2.2.1))) := by
        apply Finset.sum_congr rfl
        intro q _
        dsimp only [P]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = ∑ a : Fin m, rho x * ∑ q : Q, c q *
          (J x a q.2.2.2 q.1 *
            (psi x * T x a q.2.1 q.2.2.1 + dpsi a x * H x q.2.1 q.2.2.1)) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = ∑ a : Fin m, rho x *
          (psi x * (2 * (B * T x a * B * J x a).trace) +
           dpsi a x * (2 * (B * H x * B * J x a).trace)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [show (∑ q : Q, c q *
          (J x a q.2.2.2 q.1 *
            (psi x * T x a q.2.1 q.2.2.1 + dpsi a x * H x q.2.1 q.2.2.1))) =
          psi x * (2 * (B * T x a * B * J x a).trace) +
           dpsi a x * (2 * (B * H x * B * J x a).trace) from
          trace_quadratic_test_pair_contraction B (H x) (J x a) (T x a) (psi x) (dpsi a x)]
      _ = A x + C x := by
        simp only [A, C, mul_add, mul_assoc, Finset.sum_add_distrib]
  have hFK (x) : (∑ q : Q, c q * F q x) = K x := by
    calc
      _ = rho x * ∑ q : Q, c q *
          (E x q.2.2.2 q.1 * (psi x * H x q.2.1 q.2.2.1)) := by
        simp only [F, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = K x := by
        rw [show (∑ q : Q, c q *
          (E x q.2.2.2 q.1 * (psi x * H x q.2.1 q.2.2.1))) =
          psi x * (2 * (B * H x * B * E x).trace) from
          trace_quadratic_forcing_contraction B (H x) (E x) (psi x)]
        simp only [K, mul_assoc]
  have hA : Integrable A mu := integrable_finsetSum _ fun a _ => hTensor a
  have hC : Integrable C mu := integrable_finsetSum _ fun a _ => hFlux a
  have hK : Integrable K mu := hTraceForce
  have hI : (∫ x, A x + C x ∂mu) = -(∫ x, K x ∂mu) := by
    calc
      _ = ∫ x, ∑ q : Q, c q * P q x ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hPC x).symm)
      _ = ∑ q : Q, c q * ∫ x, P q x ∂mu := by
        rw [integral_finsetSum _ (fun q _ => (hP q).const_mul (c q))]
        simp only [integral_const_mul]
      _ = ∑ q : Q, -(c q * ∫ x, F q x ∂mu) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [show (∫ x, P q x ∂mu) = -(∫ x, F q x ∂mu) from
          hTest q.2.1 q.2.2.1 q.2.2.2 q.1]
        ring
      _ = -(∫ x, ∑ q : Q, c q * F q x ∂mu) := by
        rw [integral_finsetSum _ (fun q _ => (hF q).const_mul (c q))]
        simp only [integral_const_mul, Finset.sum_neg_distrib]
      _ = -(∫ x, K x ∂mu) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall hFK)
  rw [integral_add hA hC] at hI
  have hLeft : (fun x => rho x *
      (∑ a : Fin m, (2 * (B * H x * B * J x a).trace) * dpsi a x)) = C := by
    funext x
    dsimp only [C]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hRight : (fun x => rho x *
      (2 * (B * H x * B * E x).trace +
        ∑ a : Fin m, 2 * (B * T x a * B * J x a).trace) * psi x) =
      (fun x => K x + A x) := by
    funext x
    dsimp only [K, A]
    simp only [add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro a _
      ring
  rw [hLeft, hRight, integral_add hK hA]
  linarith

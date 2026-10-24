-- Prove2me | solution 1 for FunctionalInequalities.Analysis.bounded_trace_quadratic_weak_derivative_data_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:06:11.443413+00:00
-- url     : https://prove2.me/submissions/e3ac1f40-df99-4e0d-ba85-aff456d2d627

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
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_408915f

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
section BoundedTraceQuadratic
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology
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
/-- For a globally bounded measurable matrix field `A` with compact-local L2 weak entry derivatives `DA`, the
trace quadratic `tr(B A B A)` is globally bounded, locally integrable, and has the weak coordinate derivatives
`2 tr(B A B DAₖ)`, which are L2 on every compact set. All finite dimensions are allowed. -/
theorem solution {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (DA : Fin d → EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    {M : NNReal}
    (hmeas : ∀ i j, Measurable (fun x => A x i j))
    (hbound : ∀ x i j, ‖A x i j‖ ≤ (M : ℝ))
    (hweak : ∀ k i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x i j) (fun x => DA k x i j)
      (EuclideanSpace.basisFun (Fin d) ℝ k))
    (hDA2 : ∀ k i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA k x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖(B * A x * B * A x).trace‖ ≤ C) ∧
      LocallyIntegrable (fun x => (B * A x * B * A x).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin d))) ∧
      ∀ k : Fin d,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
          (fun x => 2 * (B * A x * B * DA k x).trace)
          (EuclideanSpace.basisFun (Fin d) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
          MemLp (fun x => 2 * (B * A x * B * DA k x).trace) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  classical
  let C : ℝ := ∑ q : Fin n × Fin n × Fin n × Fin n,
    ‖B q.1 q.2.1 * B q.2.2.1 q.2.2.2‖ * (M : ℝ) ^ 2
  have hb (x : EuclideanSpace ℝ (Fin d)) : ‖(B * A x * B * A x).trace‖ ≤ C := by
    rw [FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_408915f]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_mul]
    have h1 := hbound x q.2.1 q.2.2.1
    have h2 := hbound x q.2.2.2 q.1
    simpa only [pow_two] using mul_le_mul h1 h2
      (norm_nonneg (A x q.2.2.2 q.1)) (NNReal.coe_nonneg M)
  have hmeasf : Measurable (fun x => (B * A x * B * A x).trace) := by
    simp_rw [FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_408915f]
    fun_prop
  have htop : MemLp (fun x => (B * A x * B * A x).trace) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    memLp_top_of_bound hmeasf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  have htopA (i j : Fin n) : MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    memLp_top_of_bound (hmeas i j).aestronglyMeasurable (M : ℝ)
      (Filter.Eventually.of_forall fun x => hbound x i j)
  refine ⟨C, Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)),
    hb, htop.locallyIntegrable le_top, ?_⟩
  intro k
  exact FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_408915f B
    (fun i j => hweak k i j) htopA (fun i j => hDA2 k i j)

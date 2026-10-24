-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:04:41.981969+00:00
-- url     : https://prove2.me/submissions/5d204486-9de7-4b65-9a8c-08ac3b3a8ec3

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
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_memLp_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_408915f

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private theorem FunctionalInequalities.Analysis.trace_product_derivative_eq {n : ℕ} (B H T : Matrix (Fin n) (Fin n) ℝ) :
    (∑ q : Fin n × Fin n × Fin n × Fin n,
      (B q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
        (T q.2.1 q.2.2.1 * H q.2.2.2 q.1 +
          H q.2.1 q.2.2.1 * T q.2.2.2 q.1)) =
      2 * (B * H * B * T).trace := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← trace_mul_mul_mul_eq_sum_408915f B T B H, ← trace_mul_mul_mul_eq_sum_408915f B H B T]
  have hcycle : (B * T * B * H).trace = (B * H * B * T).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * T) (B * H)
  rw [hcycle]
  ring
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- A bounded weak matrix field has the exact first directional derivative
of trace(B A B A), with locally L2 density, for arbitrary constant real B. -/
theorem solution {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
      (fun x => 2 * (B * A x * B * DA x).trace) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => 2 * (B * A x * B * DA x).trace) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  have hprod := fun q : Fin n × Fin n × Fin n × Fin n =>
    (hA q.2.1 q.2.2.1).mul_of_locally_memLp_two_408915f
      (hA q.2.2.2 q.1)
      (hbound q.2.1 q.2.2.1) (hbound q.2.2.2 q.1)
      (hDA2 q.2.1 q.2.2.1) (hDA2 q.2.2.2 q.1)
  have hsum := FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_408915f
    (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n))
    (fun q => B q.1 q.2.1 * B q.2.2.1 q.2.2.2)
    (f := fun q x => A x q.2.1 q.2.2.1 * A x q.2.2.2 q.1)
    (df := fun q x =>
      DA x q.2.1 q.2.2.1 * A x q.2.2.2 q.1 +
        A x q.2.1 q.2.2.1 * DA x q.2.2.2 q.1)
    (v := v)
    (fun q _ => (hprod q).1)
    (fun q _ => (hprod q).2)
  simpa only [← FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_408915f, trace_product_derivative_eq] using hsum

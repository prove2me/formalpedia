-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:08.971034+00:00
-- url     : https://prove2.me/submissions/e20f7934-72cc-4543-b266-529f29d88a81

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_memLp_two_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_readable
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_readable

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
private theorem FunctionalInequalities.Analysis.trace_product_derivative_eq {n : ℕ} (B H T : Matrix (Fin n) (Fin n) ℝ) :
    (∑ q : Fin n × Fin n × Fin n × Fin n,
      (B q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
        (T q.2.1 q.2.2.1 * H q.2.2.2 q.1 +
          H q.2.1 q.2.2.1 * T q.2.2.2 q.1)) =
      2 * (B * H * B * T).trace := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← trace_mul_mul_mul_eq_sum_readable B T B H, ← trace_mul_mul_mul_eq_sum_readable B H B T]
  have hcycle : (B * T * B * H).trace = (B * H * B * T).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * T) (B * H)
  rw [hcycle]
  ring
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
    (hA q.2.1 q.2.2.1).mul_of_locally_memLp_two_readable
      (hA q.2.2.2 q.1)
      (hbound q.2.1 q.2.2.1) (hbound q.2.2.2 q.1)
      (hDA2 q.2.1 q.2.2.1) (hDA2 q.2.2.2 q.1)
  have hsum := FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_readable
    (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n))
    (fun q => B q.1 q.2.1 * B q.2.2.1 q.2.2.2)
    (f := fun q x => A x q.2.1 q.2.2.1 * A x q.2.2.2 q.1)
    (df := fun q x =>
      DA x q.2.1 q.2.2.1 * A x q.2.2.2 q.1 +
        A x q.2.1 q.2.2.1 * DA x q.2.2.2 q.1)
    (v := v)
    (fun q _ => (hprod q).1)
    (fun q _ => (hprod q).2)
  simpa only [← FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_readable, FunctionalInequalities.Analysis.trace_product_derivative_eq] using hsum

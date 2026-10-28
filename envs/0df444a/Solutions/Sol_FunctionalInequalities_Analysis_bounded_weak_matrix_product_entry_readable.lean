-- Prove2me | solution 1 for FunctionalInequalities.Analysis.bounded_weak_matrix_product_entry_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:12.863158+00:00
-- url     : https://prove2.me/submissions/e44f9980-5829-4b5a-ac34-19ce6725523e

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_readable

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
section BoundedWeakMatrixProduct
open MeasureTheory Matrix
private theorem FunctionalInequalities.Analysis.matrix_product_entry_eq_sum {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : (S * A * S) i j =
    ∑ q : Fin n × Fin n, (S i q.1 * S q.2 j) * A q.1 q.2 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring
set_option maxHeartbeats 1000000 in
/-- For a constant real matrix `S` and a matrix field `H` with globally bounded entries and compact-local L2 weak entry
derivatives `DHₖ`, every entry of the two-sided product `S H S` is globally bounded with weak derivatives the entries of
`S DHₖ S`, L2 on compact sets. Arbitrary finite ambient and matrix dimensions, including zero. -/
theorem solution {d n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    {H DH : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin d)} (M : ℝ)
    (hH : ∀ a b, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => H x a b) (fun x => DH x a b) v)
    (hbound : ∀ x a b, ‖H x a b‖ ≤ M)
    (hD : ∀ a b, ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      MemLp (fun x => DH x a b) 2 ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K))
    (i j : Fin n) :
    (∀ x, ‖(S * H x * S) i j‖ ≤
      ∑ q : Fin n × Fin n, ‖S i q.1 * S q.2 j‖ * max M 0) ∧
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (S * H x * S) i j) (fun x => (S * DH x * S) i j) v ∧
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      MemLp (fun x => (S * DH x * S) i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K) := by
  classical
  have hsum := FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_readable
    (Finset.univ : Finset (Fin n × Fin n)) (fun q => S i q.1 * S q.2 j)
    (f := fun q x => H x q.1 q.2) (df := fun q x => DH x q.1 q.2) (v := v)
    (fun q _ => hH q.1 q.2) (fun q _ => hD q.1 q.2)
  have hweak : FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (S * H x * S) i j)
      (fun x => (S * DH x * S) i j) v ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
        MemLp (fun x => (S * DH x * S) i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K) := by
    simpa only [← FunctionalInequalities.Analysis.matrix_product_entry_eq_sum] using hsum
  refine ⟨?_, hweak.1, hweak.2⟩
  intro x
  rw [FunctionalInequalities.Analysis.matrix_product_entry_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((hbound x q.1 q.2).trans (le_max_left M 0)) (norm_nonneg _)

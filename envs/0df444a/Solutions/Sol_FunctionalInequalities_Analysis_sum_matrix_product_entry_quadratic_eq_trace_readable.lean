-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_matrix_product_entry_quadratic_eq_trace_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:07.345926+00:00
-- url     : https://prove2.me/submissions/0631af50-b6cf-430e-acc7-140c16ef9be0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra
import Theorems.Thm_FunctionalInequalities_Analysis_sum_matrix_product_entry_mul_eq_trace_readable

open Matrix
section MatrixProductEntryTrace
set_option maxHeartbeats 1000000 in
/-- Entrywise inverse-quadratic energies of `S Tₖ S` sum to the trace energy `∑ₖₗ Rₖₗ tr((S S) Tₖ (S S) Tₗ)` for symmetric
`S`, `Tₖ` and an arbitrary real `R`; all finite dimensions. -/
theorem solution {m n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (T : Fin m → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ k, (T k).IsSymm) :
    (∑ p : Fin n × Fin n,
      (fun k => (S * T k * S) p.1 p.2) ⬝ᵥ
        (R *ᵥ (fun k => (S * T k * S) p.1 p.2))) =
      ∑ k : Fin m, ∑ l : Fin m, R k l * ((S * S) * T k * (S * S) * T l).trace := by
  classical
  have hOne (p : Fin n × Fin n) :
      (fun k => (S * T k * S) p.1 p.2) ⬝ᵥ
        (R *ᵥ (fun k => (S * T k * S) p.1 p.2)) =
      ∑ q : Fin m × Fin m, R q.1 q.2 *
        ((S * T q.1 * S) p.1 p.2 * (S * T q.2 * S) p.1 p.2) := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hOne]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [show (∑ i : Fin n, ∑ j : Fin n,
      (S * T k * S) i j * (S * T l * S) i j) =
      ((S * S) * T k * (S * S) * T l).trace from by
    simpa only [Fintype.sum_prod_type] using
      FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_readable S (T k) (T l) hS (hT l)]

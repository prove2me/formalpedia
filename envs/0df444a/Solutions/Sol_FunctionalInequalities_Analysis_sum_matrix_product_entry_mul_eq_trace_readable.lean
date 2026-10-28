-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:15.697909+00:00
-- url     : https://prove2.me/submissions/4b8e34ba-02a6-4fd3-aac8-3332a4c32823

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra

open Matrix
section MatrixProductEntryTrace
/-- For symmetric `S` and `D`, `∑ᵢⱼ (S A S)ᵢⱼ (S D S)ᵢⱼ = tr((S S) A (S S) D)`; all finite dimensions. -/
theorem solution {n : ℕ}
    (S A D : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) (hD : D.IsSymm) :
    (∑ p : Fin n × Fin n, (S * A * S) p.1 p.2 * (S * D * S) p.1 p.2) =
      ((S * S) * A * (S * S) * D).trace := by
  classical
  have hSt : S.transpose = S := hS
  have hDt : D.transpose = D := hD
  have hQ : (S * D * S).transpose = S * D * S := by
    simp only [Matrix.transpose_mul, hSt, hDt, Matrix.mul_assoc]
  have hentry (i j : Fin n) : (S * D * S) j i = (S * D * S) i j :=
    congrFun (congrFun hQ i) j
  calc
    _ = ((S * A * S) * (S * D * S)).trace := by
      simp only [Fintype.sum_prod_type]
      change (∑ i : Fin n, ∑ j : Fin n, (S * A * S) i j * (S * D * S) i j) =
        ∑ i : Fin n, ∑ j : Fin n, (S * A * S) i j * (S * D * S) j i
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hentry]
    _ = _ := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (S * A * S * S * D) S

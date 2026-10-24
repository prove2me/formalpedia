-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:47:30.655033+00:00
-- url     : https://prove2.me/submissions/d99b1e8a-0a72-4569-b503-b5a33fd41d4e

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

open Matrix
section MatrixProductEntryTrace
open Matrix
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

-- Prove2me | solution 1 for BookProof.ChapterCollapseDiagonal.trace_diag_nullDiag_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:38:58.551589+00:00
-- url     : https://prove2.me/submissions/dac7dc1e-1a7e-4848-824b-34d472b039b0

-- Generated from ChapterCollapseDiagonal.lean — solution of BookProof.ChapterCollapseDiagonal.trace_diag_nullDiag_zero
import Mathlib
import Definitions.Def_ChapterCollapseDiagonal
import Theorems.Thm_BookProof_ChapterCollapseDiagonal_trace_diagonal_mul
open BookProof.ChapterCollapseDiagonal



open scoped BigOperators
open Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (ρ O : Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsDiagonal ρ) (hO : ∀ i, O i i = 0) :
    (ρ * O).trace = 0 := by

  rw [trace_diagonal_mul ρ O hρ]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [hO i, mul_zero]

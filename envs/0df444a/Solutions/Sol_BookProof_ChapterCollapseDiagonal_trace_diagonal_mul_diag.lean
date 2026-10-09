-- Prove2me | solution 1 for BookProof.ChapterCollapseDiagonal.trace_diagonal_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:38:59.67324+00:00
-- url     : https://prove2.me/submissions/08ca7bf0-fefe-45c4-adfa-b72f646ccb3c

-- Generated from ChapterCollapseDiagonal.lean — solution of BookProof.ChapterCollapseDiagonal.trace_diagonal_mul_diag
import Mathlib
import Definitions.Def_ChapterCollapseDiagonal
import Theorems.Thm_BookProof_ChapterCollapseDiagonal_trace_diagonal_mul
open BookProof.ChapterCollapseDiagonal



open scoped BigOperators
open Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (ρ D : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) :
    (ρ * D).trace = ∑ i, ρ i i * D i i := trace_diagonal_mul ρ D hρ

-- Prove2me | solution 1 for BookProof.AbelianDiagonal.commutant_diagonal_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:50:26.110072+00:00
-- url     : https://prove2.me/submissions/ff14e4ad-cd49-4c65-a8fa-35d3a8432885

import Mathlib
import Definitions.Def_ChapterAbelianDiagonal
open Matrix BookProof.AbelianDiagonal
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution (M : Matrix n n ℂ)
    (h : ∀ d : n → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have he := congrArg (fun A : Matrix n n ℂ => A i j) (h (fun k => if k = j then 1 else 0))
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, hij] using he

#print axioms solution


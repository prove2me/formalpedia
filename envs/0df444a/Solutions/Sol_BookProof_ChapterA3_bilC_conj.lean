-- Prove2me | solution 1 for BookProof.ChapterA3.bilC_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:34:12.187242+00:00
-- url     : https://prove2.me/submissions/9e066687-5a74-4b96-875e-e670dab8c325

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.bilC_conj
import Mathlib
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (A M : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℂ) :
    bilC (Aᵀ * M * A) x = bilC M (fun i => ∑ j, A i j * x j) := by

  unfold bilC; simp [ Matrix.mul_apply, Fin.sum_univ_four ] ; ring!;

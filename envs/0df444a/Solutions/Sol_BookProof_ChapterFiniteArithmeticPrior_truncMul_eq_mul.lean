-- Prove2me | solution 1 for BookProof.ChapterFiniteArithmeticPrior.truncMul_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:11:38.104965+00:00
-- url     : https://prove2.me/submissions/cbd65d99-0c22-4cde-8cd2-f1aae1662ba0

-- Generated from ChapterFiniteArithmeticPrior.lean — solution of BookProof.ChapterFiniteArithmeticPrior.truncMul_eq_mul
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
open BookProof.ChapterFiniteArithmeticPrior

set_option maxHeartbeats 1000000 in
theorem solution {B : ℕ} [NeZero B] (a b : Fin B) (h : (a : ℕ) * (b : ℕ) < B) :
    (((truncMul B).result a b : Fin B) : ℕ) = (a : ℕ) * (b : ℕ) := by

  simp [truncMul, h]

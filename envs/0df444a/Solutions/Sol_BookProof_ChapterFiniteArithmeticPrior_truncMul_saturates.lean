-- Prove2me | solution 1 for BookProof.ChapterFiniteArithmeticPrior.truncMul_saturates
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:12:26.340005+00:00
-- url     : https://prove2.me/submissions/14e0b420-2388-4821-85e4-04b2c6db9c7b

-- Generated from ChapterFiniteArithmeticPrior.lean — solution of BookProof.ChapterFiniteArithmeticPrior.truncMul_saturates
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
open BookProof.ChapterFiniteArithmeticPrior

set_option maxHeartbeats 1000000 in
theorem solution {B : ℕ} [NeZero B] (a b : Fin B)
    (h : ¬ (a : ℕ) * (b : ℕ) < B) :
    (((truncMul B).result a b : Fin B) : ℕ) = B - 1 := by

  simp [truncMul, h]

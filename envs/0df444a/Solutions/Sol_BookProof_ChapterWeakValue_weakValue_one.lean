-- Prove2me | solution 1 for BookProof.ChapterWeakValue.weakValue_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:22.862323+00:00
-- url     : https://prove2.me/submissions/1051ec71-2afb-4b8a-a03c-3723fad18115

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.weakValue_one
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i f : Fin n → ℂ) (h : ip f i ≠ 0) :
    weakValue i f (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by

  rw [weakValue, Matrix.one_mulVec, div_self h]

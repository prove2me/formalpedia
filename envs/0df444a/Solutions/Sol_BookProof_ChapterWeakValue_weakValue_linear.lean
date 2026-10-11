-- Prove2me | solution 1 for BookProof.ChapterWeakValue.weakValue_linear
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:21.473282+00:00
-- url     : https://prove2.me/submissions/847d7d4b-e7a8-46de-b637-70e15a740133

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.weakValue_linear
import Mathlib
import Definitions.Def_ChapterWeakValue
import Theorems.Thm_BookProof_ChapterWeakValue_weakValue_add
import Theorems.Thm_BookProof_ChapterWeakValue_weakValue_smul
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c d : ℂ) (i f : Fin n → ℂ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    weakValue i f (c • A + d • B) =
      c * weakValue i f A + d * weakValue i f B := by

  rw [weakValue_add, weakValue_smul, weakValue_smul]

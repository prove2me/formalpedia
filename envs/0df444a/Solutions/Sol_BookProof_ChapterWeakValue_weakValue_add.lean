-- Prove2me | solution 1 for BookProof.ChapterWeakValue.weakValue_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:18.724855+00:00
-- url     : https://prove2.me/submissions/0c4eb2b9-bfda-4970-b721-a9a613d4d3a7

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.weakValue_add
import Mathlib
import Definitions.Def_ChapterWeakValue
import Theorems.Thm_BookProof_ChapterWeakValue_ip_add_right
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i f : Fin n → ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    weakValue i f (A + B) = weakValue i f A + weakValue i f B := by

  rw [weakValue, weakValue, weakValue, Matrix.add_mulVec, ip_add_right, add_div]

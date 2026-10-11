-- Prove2me | solution 1 for BookProof.ChapterWeakValue.weakValue_proj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:29.416905+00:00
-- url     : https://prove2.me/submissions/ab126fa4-df33-401c-9f7a-925f876a4682

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.weakValue_proj
import Mathlib
import Definitions.Def_ChapterWeakValue
import Theorems.Thm_BookProof_ChapterWeakValue_ip_projMat
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i f : Fin n → ℂ) (a : Fin n) :
    weakValue i f (projMat a) = starRingEnd ℂ (f a) * i a / ip f i := by

  rw [weakValue, ip_projMat]

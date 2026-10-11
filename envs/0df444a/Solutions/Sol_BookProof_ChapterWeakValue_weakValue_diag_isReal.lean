-- Prove2me | solution 1 for BookProof.ChapterWeakValue.weakValue_diag_isReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:17.447242+00:00
-- url     : https://prove2.me/submissions/359528ad-3b0f-4225-a2f7-d2ec8e92c245

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.weakValue_diag_isReal
import Mathlib
import Definitions.Def_ChapterWeakValue
import Theorems.Thm_BookProof_ChapterWeakValue_ip_conj_mulVec
import Theorems.Thm_BookProof_ChapterWeakValue_weakValue_diag
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Aᴴ = A) (hi : ip i i = 1) :
    starRingEnd ℂ (weakValue i i A) = weakValue i i A := by

  rw [weakValue_diag i A hi, ip_conj_mulVec, hA]

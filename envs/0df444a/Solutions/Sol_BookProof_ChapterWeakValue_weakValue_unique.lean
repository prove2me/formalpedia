-- Prove2me | solution 1 for BookProof.ChapterWeakValue.weakValue_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:14.436622+00:00
-- url     : https://prove2.me/submissions/16682304-ea65-421d-8cae-cd8b20740257

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.weakValue_unique
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ip f i ≠ 0) (w : ℂ) (hw : w * ip f i = ip f (A *ᵥ i)) :
    w = weakValue i f A := by

  rw [weakValue, eq_div_iff h, hw]

-- Prove2me | solution 1 for BookProof.ChapterWeakValue.projMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:24.127435+00:00
-- url     : https://prove2.me/submissions/3bff9319-c74c-43d6-b26f-6efa3fe5e720

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.projMat_mulVec
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin n) (v : Fin n → ℂ) (b : Fin n) :
    (projMat a *ᵥ v) b = if b = a then v a else 0 := by

  by_cases hb : b = a <;>
    simp [projMat, Matrix.mulVec, dotProduct, hb, Finset.sum_ite_eq']

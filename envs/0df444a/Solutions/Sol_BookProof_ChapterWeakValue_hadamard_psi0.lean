-- Prove2me | solution 1 for BookProof.ChapterWeakValue.hadamard_psi0
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:45:52.385576+00:00
-- url     : https://prove2.me/submissions/d10594f3-3a1c-4890-be95-4b2a281c0930

-- Generated from ChapterWeakValue.lean — solution of BookProof.ChapterWeakValue.hadamard_psi0
import Mathlib
import Definitions.Def_ChapterWeakValue
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterWeakValue



open scoped BigOperators Matrix
open BookProof.ChapterDoubleSlit


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution : (H *ᵥ psi0) = ![(1 / Real.sqrt 2 : ℂ), (1 / Real.sqrt 2 : ℂ)] := by
  funext b
  fin_cases b <;>
    simp [H, psi0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

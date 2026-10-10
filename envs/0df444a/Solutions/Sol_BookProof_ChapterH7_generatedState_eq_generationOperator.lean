-- Prove2me | solution 1 for BookProof.ChapterH7.generatedState_eq_generationOperator
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:37:45.323803+00:00
-- url     : https://prove2.me/submissions/3873ef5f-1a95-4f18-9522-45e5d9dd43d1

-- Generated from ChapterH7.lean — solution of BookProof.ChapterH7.generatedState_eq_generationOperator
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
open BookProof.ChapterH7



noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6
open BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    (psi0 : Fin m → ℂ) :
    generatedState A (t : ℂ) psi0 = (generationOperator A t).mulVec psi0 := rfl

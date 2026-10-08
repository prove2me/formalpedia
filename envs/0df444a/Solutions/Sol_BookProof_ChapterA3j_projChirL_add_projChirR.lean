-- Prove2me | solution 1 for BookProof.ChapterA3j.projChirL_add_projChirR
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:30:40.211983+00:00
-- url     : https://prove2.me/submissions/abe54c25-35ff-4107-9add-459c9b5b2b71

import Mathlib
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3

open Matrix
open BookProof.ChapterA3
open BookProof.ChapterA3j

theorem solution : projChirL + projChirR = 1 := by
  let a : ℂ := (2 : ℂ)⁻¹
  let x : Matrix (Fin 4) (Fin 4) ℂ := 1 - Complex.I • chir
  let y : Matrix (Fin 4) (Fin 4) ℂ := 1 + Complex.I • chir
  have hsum : x + y = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    dsimp [x, y]
    simp only [two_smul]
    abel
  have ha : a * (2 : ℂ) = 1 := by
    dsimp [a]
    norm_num
  change a • x + a • y = 1
  rw [← smul_add, hsum, smul_smul, ha]
  simp

#print axioms solution

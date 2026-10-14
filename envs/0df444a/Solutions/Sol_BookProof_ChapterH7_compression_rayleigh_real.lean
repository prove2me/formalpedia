-- Prove2me | solution 1 for BookProof.ChapterH7.compression_rayleigh_real
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:01.718799+00:00
-- url     : https://prove2.me/submissions/f4e620ae-89d2-499e-b93f-e4f3c6bbe242

-- Generated from ChapterH7.lean — solution of BookProof.ChapterH7.compression_rayleigh_real
import Mathlib
import Definitions.Def_ChapterH7
import Theorems.Thm_BookProof_ChapterH7_inner_self_real
import Theorems.Thm_BookProof_ChapterH6_krylov_rayleigh_transfer
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH7



noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hX : IsSelfAdjoint X) (y : F) : (inner ℂ y (compress V X y) : ℂ).im = 0 := by

  rw [krylov_rayleigh_transfer]
  exact inner_self_real X hX (V y)

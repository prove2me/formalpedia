-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:32.366857+00:00
-- url     : https://prove2.me/submissions/2138e4a9-f432-4280-855f-967ca093aa81

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_littleGroup_null
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_exists_boost_null
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_littleGroup_conj
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 4 → ℝ) (hp0 : 0 < p 0)
    (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      littleGroup p = (fun B => A * B * A⁻¹) '' SE2 := by

  obtain ⟨A, hA, hAp⟩ := exists_boost_null p hp0 hshell
  exact ⟨A, hA, by rw [littleGroup_conj hA hAp, littleGroup_null]⟩

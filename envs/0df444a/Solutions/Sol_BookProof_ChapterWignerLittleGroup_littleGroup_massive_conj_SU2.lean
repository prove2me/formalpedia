-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:29.816442+00:00
-- url     : https://prove2.me/submissions/8c4969a1-5998-43c0-bcba-a13acd601520

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_littleGroup_rest
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_exists_boost_massive
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_littleGroup_conj
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hp0 : 0 < p 0)
    (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = m ^ 2) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      littleGroup p = (fun B => A * B * A⁻¹) '' SU2 := by

  obtain ⟨A, hA, hAp⟩ := exists_boost_massive hm p hp0 hshell
  exact ⟨A, hA, by rw [littleGroup_conj hA hAp, littleGroup_rest (ne_of_gt hm)]⟩

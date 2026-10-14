-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:22.389045+00:00
-- url     : https://prove2.me/submissions/93a0c974-8f3f-40e0-bc94-1eac317c219c

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_exists_boost_spacelike_of_pos
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_exists_boost_spacelike_of_neg
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_exists_boost_spacelike_of_zero
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ)
    (hshell : minkSq p = -m ^ 2) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by

  rcases lt_trichotomy (p 0 + p 3) 0 with h | h | h
  · exact exists_boost_spacelike_of_neg hm p hshell h
  · exact exists_boost_spacelike_of_zero hm p hshell h
  · exact exists_boost_spacelike_of_pos hm p hshell h

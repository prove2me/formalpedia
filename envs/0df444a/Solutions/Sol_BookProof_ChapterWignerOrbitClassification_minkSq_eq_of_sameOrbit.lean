-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.minkSq_eq_of_sameOrbit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:44.185752+00:00
-- url     : https://prove2.me/submissions/ddc84d7b-58b5-4298-8e6a-b0b2060ca6cc

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.minkSq_eq_of_sameOrbit
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_mass_invariant
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {p q : Fin 4 → ℝ} (h : SameOrbit p q) : minkSq p = minkSq q := by

  obtain ⟨A, hA, hact⟩ := h
  exact (mass_invariant hA hact).symm

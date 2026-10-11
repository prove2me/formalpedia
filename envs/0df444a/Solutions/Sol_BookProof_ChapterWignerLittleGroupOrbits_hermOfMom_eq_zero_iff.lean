-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:36.134612+00:00
-- url     : https://prove2.me/submissions/894898af-9ad0-4fb5-8ac6-fb083a121fe1

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_injective
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_zero
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin 4 → ℝ} : hermOfMom p = 0 ↔ ∀ i, p i = 0 := by

  constructor
  · intro h
    have := hermOfMom_injective (q := fun _ => 0) (by rw [h, hermOfMom_zero])
    simpa using this
  · intro h
    have : hermOfMom p = hermOfMom (fun _ => 0) := by
      congr 1
      funext i
      simp [h i]
    rw [this, hermOfMom_zero]

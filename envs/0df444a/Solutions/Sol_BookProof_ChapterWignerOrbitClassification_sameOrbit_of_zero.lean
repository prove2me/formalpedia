-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.sameOrbit_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:54:09.2166+00:00
-- url     : https://prove2.me/submissions/4a0f90d2-5706-4af4-bcf4-edb5eabef19b

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.sameOrbit_of_zero
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_eq_zero_iff
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {p q : Fin 4 → ℝ} (hp : ∀ i, p i = 0) (hq : ∀ i, q i = 0) :
    SameOrbit p q := by

  refine ⟨1, by simp, ?_⟩
  rw [hermOfMom_eq_zero_iff.2 hp, hermOfMom_eq_zero_iff.2 hq, act, Matrix.mul_zero,
    Matrix.zero_mul]

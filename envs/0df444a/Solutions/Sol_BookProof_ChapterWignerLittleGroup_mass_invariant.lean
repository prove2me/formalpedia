-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.mass_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:13.857977+00:00
-- url     : https://prove2.me/submissions/4d327c64-8e37-450d-ac74-291915b65f9c

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.mass_invariant
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_det
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_det_of_sl
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ}
    (h : act A (hermOfMom p) = hermOfMom q) :
    q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := by

  have := congrArg Matrix.det h
  rw [act_det_of_sl _ _ hA, hermOfMom_det, hermOfMom_det] at this
  exact_mod_cast this.symm

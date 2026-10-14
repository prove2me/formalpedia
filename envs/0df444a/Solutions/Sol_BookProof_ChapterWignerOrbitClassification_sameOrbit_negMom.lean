-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.sameOrbit_negMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:39.634455+00:00
-- url     : https://prove2.me/submissions/5f655778-4758-42ac-b732-91e6b6a5689b

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.sameOrbit_negMom
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_hermOfMom_negMom
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {p q : Fin 4 → ℝ} (h : SameOrbit p q) :
    SameOrbit (negMom p) (negMom q) := by

  obtain ⟨A, hA, hact⟩ := h
  refine ⟨A, hA, ?_⟩
  simp only [act] at hact ⊢
  rw [hermOfMom_negMom, hermOfMom_negMom, Matrix.mul_neg, Matrix.neg_mul, hact]

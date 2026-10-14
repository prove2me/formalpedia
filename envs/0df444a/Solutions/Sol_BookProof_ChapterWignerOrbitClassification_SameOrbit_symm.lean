-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.SameOrbit.symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:42.033373+00:00
-- url     : https://prove2.me/submissions/6c50aca0-a984-44a1-a5ef-510502ed5330

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.SameOrbit.symm
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_act_inv_of_act
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_det_inv_eq_one
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {p q : Fin 4 → ℝ} (h : SameOrbit p q) : SameOrbit q p := by

  obtain ⟨A, hA, hact⟩ := h
  exact ⟨A⁻¹, det_inv_eq_one hA, act_inv_of_act hA hact⟩

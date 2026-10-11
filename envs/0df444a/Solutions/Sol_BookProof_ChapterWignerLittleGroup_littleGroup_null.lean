-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.littleGroup_null
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:19.569643+00:00
-- url     : https://prove2.me/submissions/64f26cc6-11f9-489b-b22e-40aae2c22c43

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.littleGroup_null
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_nullMom
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution : littleGroup nullMom = SE2 := by

  ext A
  simp only [littleGroup, SE2, Set.mem_setOf_eq, hermOfMom_nullMom, act]
  constructor
  · rintro ⟨hdet, h⟩
    have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      rw [Matrix.det_fin_two] at hdet; exact hdet
    have h11 : A 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using
        congrFun (congrFun h 1) 1
    have h00 : A 0 0 * 2 * (starRingEnd ℂ) (A 0 0) = 2 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using
        congrFun (congrFun h 0) 0
    have ha : A 0 0 * (starRingEnd ℂ) (A 0 0) = 1 := by linear_combination h00 / 2
    have h0 : A 0 0 ≠ 0 := by
      intro h0
      rw [h0] at ha; simp at ha
    have h1 : A 1 1 = (starRingEnd ℂ) (A 0 0) := by
      have hmul : A 0 0 * A 1 1 = 1 := by rw [h11] at hdet'; linear_combination hdet'
      refine mul_left_cancel₀ h0 ?_
      rw [hmul, ha]
    refine ⟨A 0 0, A 0 1, ha, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11, h1]
  · rintro ⟨a, b, ha, rfl⟩
    refine ⟨by simp [Matrix.det_fin_two_of]; linear_combination ha, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    linear_combination 2 * ha

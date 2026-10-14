-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:24.122237+00:00
-- url     : https://prove2.me/submissions/240ba881-b3c2-40ee-9c0f-cebf2e6a26e4

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_hermOfMom_spaceRefMom
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_exists_boost_spacelike
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_littleGroup_conj
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterLittleGroup
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin 4 → ℝ} (hneg : minkSq p < 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      littleGroup p = (fun B => A * B * A⁻¹) '' SU11 := by

  set m : ℝ := Real.sqrt (-minkSq p) with hm
  have hmpos : 0 < m := Real.sqrt_pos.2 (by linarith)
  have hm2 : m ^ 2 = -minkSq p := Real.sq_sqrt (by linarith)
  have hp : minkSq p = -m ^ 2 := by rw [hm2]; ring
  obtain ⟨A, hA, hact⟩ := exists_boost_spacelike hmpos p hp
  refine ⟨A, hA, ?_⟩
  have hconj := littleGroup_conj hA hact
  rw [hconj]
  congr 1
  -- the little group of `(0,0,0,m)` is that of `(0,0,0,1)`, namely `SU(1,1)`
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hmpos
  have hE : !![(m : ℂ), 0; 0, -(m : ℂ)] = (m : ℂ) • !![(1 : ℂ), 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have key : ∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      B * !![(m : ℂ), 0; 0, -(m : ℂ)] * Bᴴ = (m : ℂ) • (B * !![(1 : ℂ), 0; 0, -1] * Bᴴ) := by
    intro B
    rw [hE, Matrix.mul_smul, Matrix.smul_mul]
  have hscale : littleGroup (spaceRefMom m) = SU11 := by
    ext B
    constructor
    · rintro ⟨hdet, hfix⟩
      refine ⟨hdet, ?_⟩
      simp only [hermOfMom_spaceRefMom, act] at hfix
      rw [key B, hE] at hfix
      exact smul_right_injective _ hm0 hfix
    · rintro ⟨hdet, hfix⟩
      refine ⟨hdet, ?_⟩
      simp only [hermOfMom_spaceRefMom, act]
      rw [key B, hfix, hE]
  exact hscale

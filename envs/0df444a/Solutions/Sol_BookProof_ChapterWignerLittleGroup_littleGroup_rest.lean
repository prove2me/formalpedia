-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.littleGroup_rest
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:17.976541+00:00
-- url     : https://prove2.me/submissions/47046ec0-26f0-4737-a02e-151d1e583528

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.littleGroup_rest
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_restMom
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution {m : ℝ} (hm : m ≠ 0) : littleGroup (restMom m) = SU2 := by

  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  ext A
  simp only [littleGroup, SU2, Set.mem_setOf_eq, hermOfMom_restMom, act]
  constructor
  · rintro ⟨hdet, h⟩
    refine ⟨hdet, ?_⟩
    have h2 : (m : ℂ) • (A * Aᴴ) = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    exact smul_right_injective _ hm' h2
  · rintro ⟨hdet, h⟩
    exact ⟨hdet, by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h]⟩

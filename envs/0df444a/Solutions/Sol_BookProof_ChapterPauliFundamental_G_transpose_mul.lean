-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.G_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:27.555211+00:00
-- url     : https://prove2.me/submissions/a2565a76-8ae3-4d5b-8c27-c9885854a965

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.G_transpose_mul
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_stepT_involutive
import Theorems.Thm_BookProof_ChapterPauliFundamental_clifford_key
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_orthogonal
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_inv
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_isUnit
import Theorems.Thm_BookProof_ChapterA3_mgamma_clifford
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) (T : Finset (Fin 4)) :
    (G T)ᵀ * mgamma μ = sgnT μ (stepT μ T) • (G (stepT μ T))ᵀ := by

  set T' := stepT μ T with hT'
  have hkey : mgamma μ * G T' = sgnT μ T' • G (stepT μ T') :=
    clifford_key mgamma_clifford μ T'
  rw [hT', stepT_involutive μ T] at hkey
  have hinvT : (G T)ᵀ * G T = 1 := by
    have := G_orthogonal T
    have hdet := G_isUnit T
    calc (G T)ᵀ * G T = (G T)⁻¹ * G T := by rw [G_inv]
    _ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hinvT' : G T' * (G T')ᵀ = 1 := G_orthogonal T'
  calc (G T)ᵀ * mgamma μ
      = (G T)ᵀ * mgamma μ * (G T' * (G T')ᵀ) := by rw [hinvT', Matrix.mul_one]
    _ = (G T)ᵀ * (mgamma μ * G T') * (G T')ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = (G T)ᵀ * ((sgnT μ T') • G T) * (G T')ᵀ := by rw [hkey]
    _ = sgnT μ T' • (((G T)ᵀ * G T) * (G T')ᵀ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = sgnT μ T' • (G T')ᵀ := by rw [hinvT, Matrix.one_mul]

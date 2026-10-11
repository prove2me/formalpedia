-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.exists_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:23.839981+00:00
-- url     : https://prove2.me/submissions/e12e46fe-58e2-469e-8584-82c46233bdbd

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.exists_intertwiner
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_inter_intertwines
import Theorems.Thm_BookProof_ChapterPauliFundamental_exists_inter_ne_zero
import Theorems.Thm_BookProof_ChapterPauliFundamental_inter_isUnit
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (hA : IsCliffordC A) :
    ∃ S : M4, IsUnit S.det ∧ ∀ μ, A μ = S * mgamma μ * S⁻¹ := by

  obtain ⟨F, hF⟩ := exists_inter_ne_zero (A := A)
  refine ⟨inter A F, inter_isUnit hA hF, fun μ => ?_⟩
  have h := inter_intertwines hA F μ
  have hinv : inter A F * (inter A F)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (inter_isUnit hA hF)
  calc A μ = A μ * (inter A F * (inter A F)⁻¹) := by rw [hinv, Matrix.mul_one]
    _ = (A μ * inter A F) * (inter A F)⁻¹ := by rw [Matrix.mul_assoc]
    _ = (inter A F * mgamma μ) * (inter A F)⁻¹ := by rw [h]

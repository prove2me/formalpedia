-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.pauli_exists
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:25.017987+00:00
-- url     : https://prove2.me/submissions/f4aed8a4-98ab-4452-a2f5-83001ce82e45

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.pauli_exists
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_exists_intertwiner
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution {B : Fin 4 → M4} (hA : IsCliffordC A) (hB : IsCliffordC B) :
    ∃ S : M4, IsUnit S.det ∧ ∀ μ, B μ = S * A μ * S⁻¹ := by

  obtain ⟨P, hP, hPeq⟩ := exists_intertwiner hA
  obtain ⟨Q, hQ, hQeq⟩ := exists_intertwiner hB
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hPinv : IsUnit (P⁻¹).det := Matrix.isUnit_nonsing_inv_det P hP
  refine ⟨Q * P⁻¹, ?_, fun μ => ?_⟩
  · rw [Matrix.det_mul]
    exact hQ.mul hPinv
  · have hmul : (Q * P⁻¹)⁻¹ = P * Q⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP]
    rw [hmul, hPeq μ, hQeq μ]
    have e : (Q * P⁻¹) * (P * mgamma μ * P⁻¹) * (P * Q⁻¹)
        = Q * (P⁻¹ * P) * mgamma μ * ((P⁻¹ * P) * Q⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [e, hPP, Matrix.mul_one, Matrix.one_mul]

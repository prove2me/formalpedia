-- Prove2me | solution 1 for BookProof.ChapterA3.spinor_mul_spinorInv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:37:02.532078+00:00
-- url     : https://prove2.me/submissions/1db3abca-66dc-4e62-9fe3-dc999197d3c8

-- Generated from ChapterA3i.lean — solution of BookProof.ChapterA3.spinor_mul_spinorInv
import Mathlib
import Definitions.Def_ChapterA3i
import Theorems.Thm_BookProof_ChapterA3_sigmaC_mul_transpose
import Theorems.Thm_BookProof_ChapterA3_Treal_mul
import Theorems.Thm_BookProof_ChapterA3_Treal_one
import Theorems.Thm_BookProof_ChapterA3_T_mul_adj2
import Theorems.Thm_BookProof_ChapterA3_sigmaC_transpose_mul
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) :
    Spinor T * SpinorInv T = 1 := by

  have hmid : ((2⁻¹ : ℂ) • SigmaCᵀ) * SigmaC = 1 := by
    rw [Matrix.smul_mul, sigmaC_transpose_mul, smul_smul]; norm_num
  have hend : SigmaC * ((2⁻¹ : ℂ) • SigmaCᵀ) = 1 := by
    rw [Matrix.mul_smul, sigmaC_mul_transpose, smul_smul]; norm_num
  unfold Spinor SpinorInv
  calc SigmaC * Treal T * ((2⁻¹ : ℂ) • SigmaCᵀ)
          * (SigmaC * Treal (adj2 T) * ((2⁻¹ : ℂ) • SigmaCᵀ))
      = SigmaC * Treal T * (((2⁻¹ : ℂ) • SigmaCᵀ) * SigmaC)
          * Treal (adj2 T) * ((2⁻¹ : ℂ) • SigmaCᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = SigmaC * Treal T * Treal (adj2 T) * ((2⁻¹ : ℂ) • SigmaCᵀ) := by
        rw [hmid, Matrix.mul_one]
    _ = SigmaC * Treal (T * adj2 T) * ((2⁻¹ : ℂ) • SigmaCᵀ) := by
        rw [Treal_mul]; simp only [Matrix.mul_assoc]
    _ = SigmaC * Treal 1 * ((2⁻¹ : ℂ) • SigmaCᵀ) := by rw [T_mul_adj2 T hdet]
    _ = SigmaC * ((2⁻¹ : ℂ) • SigmaCᵀ) := by rw [Treal_one, Matrix.mul_one]
    _ = 1 := hend

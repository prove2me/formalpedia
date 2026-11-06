-- Prove2me | solution 1 for BookProof.ChapterH7.generationOperator_conjTranspose_mul
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:03:12.205299+00:00
-- url     : https://prove2.me/submissions/9616b170-3011-4790-b957-45791cfc014c

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.generationOperator_conjTranspose_mul
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterH7


noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6
open scoped Matrix

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {m : ℕ}

theorem solution (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    (hA : A.IsHermitian) :
    (generationOperator A t)ᴴ * generationOperator A t = 1 := by
  have hconj :
      (generationOperator A t)ᴴ = NormedSpace.exp ((Complex.I * (t : ℂ)) • A) := by
    rw [generationOperator, ← Matrix.exp_conjTranspose]
    congr 1
    rw [Matrix.conjTranspose_smul, hA.eq]
    congr 1
    simp [Complex.conj_I]
  have hcomm : Commute ((Complex.I * (t : ℂ)) • A) ((-Complex.I * (t : ℂ)) • A) := by
    unfold Commute SemiconjBy
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul,
      mul_comm (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ))]
  rw [hconj, generationOperator, ← Matrix.exp_add_of_commute _ _ hcomm]
  rw [← add_smul]
  rw [show (Complex.I * (t : ℂ)) + (-Complex.I * (t : ℂ)) = 0 by ring]
  simp

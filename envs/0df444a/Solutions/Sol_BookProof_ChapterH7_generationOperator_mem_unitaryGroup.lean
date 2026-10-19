-- Prove2me | solution 1 for BookProof.ChapterH7.generationOperator_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:24:59.047996+00:00
-- url     : https://prove2.me/submissions/6ca47eea-a5be-4903-83ab-8f231f738054

import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH7
-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.generationOperator_mem_unitaryGroup
open BookProof.ChapterH7


noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {m : ℕ}
theorem h44_exp_unitary {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (hA : A.IsHermitian) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • A) ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  set X := (-Complex.I * (t : ℂ)) • A with hX
  have hXs : Matrix.conjTranspose X = -X := by
    rw [hX, Matrix.conjTranspose_smul, hA.eq]
    rw [← neg_smul]; congr 1; simp
  rw [Matrix.mem_unitaryGroup_iff]
  change NormedSpace.exp X * Matrix.conjTranspose (NormedSpace.exp X) = 1
  rw [← Matrix.exp_conjTranspose, hXs, Matrix.exp_neg]
  apply Matrix.mul_nonsing_inv
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X)

theorem solution (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    (hA : A.IsHermitian) : generationOperator A t ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  exact h44_exp_unitary A t hA


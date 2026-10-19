-- Prove2me | solution 1 for BookProof.ChapterH7.generation_preserves_l2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:25:48.425836+00:00
-- url     : https://prove2.me/submissions/6cfbb089-0476-498d-8913-f34d7e0b21b4

import Definitions.Def_ChapterH4
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH6
-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.generation_preserves_l2
open BookProof.ChapterH6
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
    (hA : A.IsHermitian) (psi0 : Fin m → ℂ) :
    ∑ i, Complex.normSq (generatedState A (t : ℂ) psi0 i) = ∑ i, Complex.normSq (psi0 i) := by
  have hU := h44_exp_unitary A t hA
  rw [Matrix.mem_unitaryGroup_iff'] at hU
  unfold BookProof.ChapterH6.generatedState
  set U := NormedSpace.exp ((-Complex.I * (t : ℂ)) • A)
  apply Complex.ofReal_injective
  push_cast
  have key : ∀ w : Fin m → ℂ, ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) = star w ⬝ᵥ w := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, key, key, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  change Matrix.vecMul (star psi0) (star U * U) ⬝ᵥ psi0 = _
  rw [hU, Matrix.vecMul_one]


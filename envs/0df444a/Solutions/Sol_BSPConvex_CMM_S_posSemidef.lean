-- Prove2me | solution 1 for BSPConvex.CMM.S_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:42:05.312991+00:00
-- url     : https://prove2.me/submissions/042cf993-7f41-4f1a-bce1-7eba2a32a2f6

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

open BSPConvex.CMM in
theorem solution {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ simplex m) :
    (Smat x).PosSemidef := by
  obtain ⟨hx0, hx1⟩ := hx
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    simp only [Smat, conjTranspose_apply, Matrix.sub_apply, diagonal_apply, vecMulVec_apply, star_trivial]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
      ring
  · intro v
    set S := ∑ j, x j * v j with hS
    have e1 : ∀ i, (Smat x *ᵥ v) i = x i * v i - x i * S := by
      intro i
      rw [Smat, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
      congr 1
      simp only [mulVec, dotProduct, vecMulVec_apply]
      rw [hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have e2 : ∀ i, v i * (x i * v i - x i * S) = x i * v i ^ 2 - (x i * v i) * S := by
      intro i; ring
    have key : star v ⬝ᵥ (Smat x *ᵥ v) = ∑ i, x i * v i ^ 2 - S ^ 2 := by
      rw [star_trivial]
      simp only [dotProduct, e1]
      rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_sub_distrib, ← Finset.sum_mul, ← hS, sq]
    rw [key]
    have hcs : S ^ 2 ≤ (∑ i, x i) * ∑ i, x i * v i ^ 2 := by
      rw [hS]
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro i _; exact hx0 i
      · intro i _; exact mul_nonneg (hx0 i) (sq_nonneg _)
      · intro i _; apply le_of_eq; ring
    have hq : 0 ≤ ∑ i, x i * v i ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hx0 i) (sq_nonneg _))
    have : (∑ i, x i) * ∑ i, x i * v i ^ 2 ≤ ∑ i, x i * v i ^ 2 := by
      calc (∑ i, x i) * ∑ i, x i * v i ^ 2 ≤ 1 * ∑ i, x i * v i ^ 2 :=
            mul_le_mul_of_nonneg_right hx1 hq
        _ = ∑ i, x i * v i ^ 2 := one_mul _
    linarith

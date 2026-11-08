-- Prove2me | solution 1 for CoCoNet.Lmat_diag_dominant_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:23:04.544399+00:00
-- url     : https://prove2.me/submissions/2d73a14c-dcc6-4281-a434-70f73e2eba40

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_Lmat

open CoCoNet in
theorem solution {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hadm : IsAdmissible m W) (B C : Finset (Fin n)) :
    (∀ j, ∑ i ∈ Finset.univ.erase j, |Lmat m W B C i j| < |Lmat m W B C j j|) ∧
      IsUnit (Lmat m W B C) := by
  have hr : ∀ (F : Finset (Fin n)) i, 0 ≤ restrictTo F m i := by
    intro F i
    unfold restrictTo
    split_ifs
    · exact (hadm.m_pos i).le
    · exact le_rfl
  have hent : ∀ i j, Lmat m W B C i j = if i = j then 1 + restrictTo B m i + restrictTo C m i
      else -(W i j * restrictTo C m j) := by
    intro i j
    unfold Lmat
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.mul_diagonal,
      Matrix.sub_apply]
    split_ifs with h
    · subst h
      rw [hadm.W_diag]
      ring
    · ring
  have key : ∀ j, ∑ i ∈ Finset.univ.erase j, |Lmat m W B C i j| < |Lmat m W B C j j| := by
    intro j
    have hd : 0 < 1 + restrictTo B m j + restrictTo C m j := by linarith [hr B j, hr C j]
    rw [hent j j, if_pos rfl, abs_of_pos hd]
    have h1 : ∀ i ∈ Finset.univ.erase j, |Lmat m W B C i j| = W i j * restrictTo C m j := by
      intro i hi
      rw [hent, if_neg (Finset.ne_of_mem_erase hi), abs_neg,
        abs_of_nonneg (mul_nonneg (hadm.W_nonneg i j) (hr C j))]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
    have hsum : ∑ i ∈ Finset.univ.erase j, W i j ≤ 1 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun i _ _ => hadm.W_nonneg i j)) (hadm.colSum_le j)
    nlinarith [hr C j, hr B j]
  refine ⟨key, ?_⟩
  have hdet : (Lmat m W B C).det ≠ 0 := by
    apply det_ne_zero_of_sum_col_lt_diag
    intro k
    simpa only [Real.norm_eq_abs] using key k
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_det_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:44:40.9458+00:00
-- url     : https://prove2.me/submissions/61141c3a-2be7-4ba6-8e50-53e6da008753

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_det_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (x : R) :
    (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * (v i - 1) ^ (j : ℕ)).det =
      (Matrix.vandermonde v).det * (1 + x) ^ n := by
  have h := qk_det_eval v (fun j : Fin n => (X : R[X]) ^ (j : ℕ) + C x * (X - C 1) ^ (j : ℕ)) (by
    intro i
    refine (natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le _) ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_pow_le.trans ?_
    have := natDegree_X_sub_C_le (1 : R)
    calc (i : ℕ) * (X - C (1 : R)).natDegree ≤ (i : ℕ) * 1 := Nat.mul_le_mul_left _ this
      _ = i := mul_one _)
  have hc : ∀ i : Fin n, ((X : R[X]) ^ (i : ℕ) + C x * (X - C 1) ^ (i : ℕ)).coeff i = 1 + x := by
    intro i
    rw [coeff_add, coeff_X_pow_self, coeff_C_mul]
    have := (monic_X_sub_C (1 : R)).pow (i : ℕ)
    have h2 : ((X - C (1 : R)) ^ (i : ℕ)).coeff i = 1 := by
      nontriviality R
      have h3 : ((X - C (1 : R)) ^ (i : ℕ)).natDegree = (i : ℕ) := by
        rw [(monic_X_sub_C (1 : R)).natDegree_pow, natDegree_X_sub_C, mul_one]
      have h4 := this.coeff_natDegree
      rwa [h3] at h4
    rw [h2, mul_one]
  simp only [hc, prod_const, card_univ, Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext i j
  simp
end Formalism.InvariantFactorPaths.ColumnFamilies

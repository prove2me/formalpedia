-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cofactorVectorKernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:26.268264+00:00
-- url     : https://prove2.me/submissions/5f9c615f-2b3f-49fa-b8c1-8f9afc2b3f23

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bCons_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bCons_succ
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_consRow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_neg_one_pow_mul_neg_one_pow
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_det_submatrix_consRow_succAbove__ac784a4c22c9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : KernelRowSpace := by
  intro R _ r Y
  constructor
  · ext a
    have h := det_consRow Y (Y a)
    have h0 : (consRowMatrix (Y a) Y).det = 0 :=
      Matrix.det_zero_of_row_eq (i := 0) (j := a.succ) (Fin.succ_ne_zero a).symm (by ext j; rfl)
    rw [h0] at h
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    exact h.symm
  · intro u hu b₀
    have hA := det_consRow Y u
    rw [hu] at hA
    ext b
    simp only [Pi.smul_apply, smul_eq_mul]
    rcases Fin.eq_self_or_eq_succAbove b₀ b with hb | ⟨c, hb⟩
    · rw [hb]
      rw [Matrix.det_succ_column _ b₀, Fin.sum_univ_succ] at hA
      have t0 : (consRowMatrix u Y).submatrix (Fin.succAbove 0) b₀.succAbove =
          Y.submatrix id b₀.succAbove := by
        ext i j; simp only [Matrix.submatrix_apply, Fin.succAbove_zero, s5bCons_succ, id]
      rw [t0] at hA
      simp only [det_submatrix_consRow_succAbove', s5bCons_zero, s5bCons_succ,
        Fin.val_zero, Fin.val_succ, zero_add] at hA
      have hterm : ∀ a : Fin r, (-1 : R) ^ ((a : ℕ) + 1 + (b₀ : ℕ)) * Y a b₀ *
          ((-1) ^ (a : ℕ) * ∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a) =
          -((-1) ^ (b₀ : ℕ) * ((∑ c, u (b₀.succAbove c) *
            (Y.submatrix id b₀.succAbove).adjugate c a) * Y a b₀)) := by
        intro a
        have hs := neg_one_pow_mul_neg_one_pow (R := R) (a : ℕ)
        rw [pow_add, pow_add, pow_one]
        linear_combination (-((-1) ^ (b₀ : ℕ) * Y a b₀ * ∑ c, u (b₀.succAbove c) *
            (Y.submatrix id b₀.succAbove).adjugate c a)) * hs
      simp only [hterm, Finset.sum_neg_distrib, ← Finset.mul_sum] at hA
      have hs := neg_one_pow_mul_neg_one_pow (R := R) (b₀ : ℕ)
      simp only [Matrix.vecMul, dotProduct]
      linear_combination ((-1) ^ (b₀ : ℕ)) * hA - ((Y.submatrix id b₀.succAbove).det * u b₀ -
        ∑ a, (∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a) * Y a b₀) * hs
    · rw [hb]
      have : (((fun c => u (b₀.succAbove c)) ᵥ* (Y.submatrix id b₀.succAbove).adjugate) ᵥ* Y)
          (b₀.succAbove c) = (((fun c => u (b₀.succAbove c)) ᵥ*
            (Y.submatrix id b₀.succAbove).adjugate) ᵥ* (Y.submatrix id b₀.succAbove)) c := by
        simp [Matrix.vecMul, dotProduct]
      rw [this, Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
      simp
end Formalism.HermitianLatticeCounting.P

-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:02:18.019943+00:00
-- url     : https://prove2.me/submissions/6df075d8-01d2-41f3-8eba-8882a09300cf

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_der_det
import Theorems.Thm_Formalism_IncomingBounds_Cay_bord
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_X_mul
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_one
import Theorems.Thm_Formalism_IncomingBounds_Cay_ddet
import Theorems.Thm_Formalism_IncomingBounds_Cay_dadj
import Theorems.Thm_Formalism_IncomingBounds_Cay_omega_step
import Theorems.Thm_Formalism_IncomingBounds_Cay_step_der

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution (n s : ℕ) : ∀ (k : ℕ) (r c : Fin (k+1) → Fin n),
    (Mg K n).det ^ k * diffOp ((Mg K n).submatrix r c).det ((Mg K n).det ^ (s+1)) =
      MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) *
        ((Mg K n).det ^ s * ((adjugate (Mg K n)).submatrix c r).det)
  | 0, r, c => by
    rw [pow_zero, one_mul, det_fin_one, det_fin_one]
    have hx : ((Mg K n).submatrix r c) 0 0 = X (Sum.inl (r 0, c 0)) := rfl
    rw [hx, ← mul_one (X _), diffOp_X_mul, diffOp_one, Derivation.leibniz_pow, ddet]
    simp only [submatrix_apply, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.cast_zero, add_zero, map_add, map_natCast,
      map_one, nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel]
    push_cast
    ring
  | k+1, r, c => by
    rw [omega_step, Finset.mul_sum]
    have hsum : ∀ j : Fin (k+2),
        (Mg K n).det ^ (k+1) * (((-1 : K) ^ (j : ℕ)) • pderiv (Sum.inl (r 0, c j))
          (diffOp ((Mg K n).submatrix (r ∘ Fin.succ) (c ∘ j.succAbove)).det ((Mg K n).det ^ (s+1)))) =
        MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) * (Mg K n).det ^ s *
          ((s : MvPolynomial (PVar n) K) *
            ((-1) ^ (j : ℕ) * ((adjugate (Mg K n)).submatrix c r) j 0 *
              (((adjugate (Mg K n)).submatrix c r).submatrix j.succAbove Fin.succ).det) +
            ((adjugate (Mg K n)).submatrix c r).det) := by
      intro j
      set B := (adjugate (Mg K n)).submatrix c r with hB
      set N := B.submatrix j.succAbove Fin.succ with hN
      have IH : (Mg K n).det ^ k *
          diffOp ((Mg K n).submatrix (r ∘ Fin.succ) (c ∘ j.succAbove)).det ((Mg K n).det ^ (s+1)) =
          MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) * ((Mg K n).det ^ s * N.det) :=
        solution n s k (r ∘ Fin.succ) (c ∘ j.succAbove)
      have hterm : ∀ i p : Fin (k+1), (Mg K n).det *
          (adjugate N i p * pderiv (Sum.inl (r 0, c j)) (N p i)) =
          B j 0 * (adjugate N i p * N p i) - adjugate N i p * B (j.succAbove p) 0 * B j i.succ := by
        intro i p
        have := dadj (K := K) (r 0) (c j) (c (j.succAbove p)) (r i.succ)
        have e1 : N p i = adjugate (Mg K n) (c (j.succAbove p)) (r i.succ) := rfl
        have e2 : B j 0 = adjugate (Mg K n) (c j) (r 0) := rfl
        have e3 : B (j.succAbove p) 0 = adjugate (Mg K n) (c (j.succAbove p)) (r 0) := rfl
        have e4 : B j i.succ = adjugate (Mg K n) (c j) (r i.succ) := rfl
        rw [e1, e2, e3, e4]
        linear_combination (adjugate N i p) * this
      have htr : ∑ i : Fin (k+1), ∑ p : Fin (k+1), adjugate N i p * N p i = ((k : MvPolynomial (PVar n) K) + 1) * N.det := by
        have h := adjugate_mul N
        have : ∀ i, ∑ p : Fin (k+1), adjugate N i p * N p i = N.det := by
          intro i
          have := congrFun (congrFun h i) i
          rw [mul_apply] at this
          rw [this]; simp
        simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
      have E3 : (Mg K n).det * pderiv (Sum.inl (r 0, c j)) N.det =
          B j 0 * ((k : MvPolynomial (PVar n) K) + 1) * N.det -
            ∑ q : Fin (k+1), ∑ p : Fin (k+1), adjugate N q p * B (j.succAbove p) 0 * B j q.succ := by
        rw [der_det, Finset.mul_sum]
        simp_rw [Finset.mul_sum, hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, htr]
        ring
      have St := step_der (pderiv (Sum.inl (r 0, c j))) ((Mg K n).det) (B j 0) N.det _ _
        (MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a))) k s (pderiv_C)
        (ddet (r 0) (c j)) IH E3
      have Bd := bord k B j
      rw [← hN] at Bd
      have hsq : ((-1 : MvPolynomial (PVar n) K) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by
        rw [← mul_pow]; simp
      rw [smul_eq_C_mul]
      simp only [map_pow, map_neg, map_one]
      linear_combination ((-1 : MvPolynomial (PVar n) K) ^ (j : ℕ)) * St
        - ((-1 : MvPolynomial (PVar n) K) ^ (j : ℕ)) *
            MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) * (Mg K n).det ^ s * Bd
        + MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) * (Mg K n).det ^ s * B.det * hsq
    rw [Finset.sum_congr rfl fun j _ => hsum j, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← det_succ_column_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.prod_range_succ _ (k+1), map_mul]
    simp only [map_add, map_natCast, map_one]
    push_cast
    ring
end Formalism.IncomingBounds.Cay

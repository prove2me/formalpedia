-- Prove2me | solution 1 for Formalism.L2.Th1.H.gaussSumEighthPower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:30.074715+00:00
-- url     : https://prove2.me/submissions/04c2c258-7ba6-439b-8a38-3e8343089b57

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_symm
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_ne
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_phi_zero
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_neg_left
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_neg_right
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_phi_neg
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_phi_orth4
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_sum_sq_of_anti
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_pow4
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.H
namespace IsQuadFn
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
end IsQuadFn
section Quaternion
variable (M : Type*) [AddCommGroup M]
end Quaternion
private theorem eq_one_of_eq_inv_mul_self_mul_inv_mul_self {a c X : ℂ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hX : X = (a⁻¹ * a) * (c⁻¹ * c)) : X = 1 := by
  rw [hX, inv_mul_cancel₀ ha, inv_mul_cancel₀ hc, one_mul]
end Formalism.L2.Th1.H
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : GaussEighth := by
  intro M _ _ φ b h
  have H := h.pow4
  have hPI : ∀ v : Fin 4 → M, ∏ i, φ (quatI M v i) = ∏ i, φ (v i) := by
    intro v
    simp only [Fin.prod_univ_four]
    change φ (-v 1) * φ (v 0) * φ (-v 3) * φ (v 2) = φ (v 0) * φ (v 1) * φ (v 2) * φ (v 3)
    simp only [h.phi_neg]
    ring
  have hPJ : ∀ v : Fin 4 → M, ∏ i, φ (quatJ M v i) = ∏ i, φ (v i) := by
    intro v
    simp only [Fin.prod_univ_four]
    change φ (-v 2) * φ (v 3) * φ (v 0) * φ (-v 1) = φ (v 0) * φ (v 1) * φ (v 2) * φ (v 3)
    simp only [h.phi_neg]
    ring
  have hPK : ∀ v : Fin 4 → M, ∏ i, φ (quatK M v i) = ∏ i, φ (v i) := by
    intro v
    simp only [Fin.prod_univ_four]
    change φ (-v 3) * φ (-v 2) * φ (v 1) * φ (v 0) = φ (v 0) * φ (v 1) * φ (v 2) * φ (v 3)
    simp only [h.phi_neg]
    ring
  have pI : ∀ v : Fin 4 → M, ∏ i, b (v i) (quatI M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (v 0) (-v 1) * b (v 1) (v 0) * b (v 2) (-v 3) * b (v 3) (v 2) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 1) (v 0), h.symm (v 3) (v 2)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 1)) (h.b_ne (v 2) (v 3)) (by ring)
  have pJ : ∀ v : Fin 4 → M, ∏ i, b (v i) (quatJ M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (v 0) (-v 2) * b (v 1) (v 3) * b (v 2) (v 0) * b (v 3) (-v 1) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 2) (v 0), h.symm (v 3) (v 1)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 2)) (h.b_ne (v 1) (v 3)) (by ring)
  have pK : ∀ v : Fin 4 → M, ∏ i, b (v i) (quatK M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (v 0) (-v 3) * b (v 1) (-v 2) * b (v 2) (v 1) * b (v 3) (v 0) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 2) (v 1), h.symm (v 3) (v 0)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 3)) (h.b_ne (v 1) (v 2)) (by ring)
  have pIJ : ∀ v : Fin 4 → M, ∏ i, b (quatI M v i) (quatJ M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (-v 1) (-v 2) * b (v 0) (v 3) * b (-v 3) (v 0) * b (v 2) (-v 1) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 3) (v 0), h.symm (v 2) (v 1)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 3)) (h.b_ne (v 1) (v 2)) (by ring)
  have pIK : ∀ v : Fin 4 → M, ∏ i, b (quatI M v i) (quatK M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (-v 1) (-v 3) * b (v 0) (-v 2) * b (-v 3) (v 1) * b (v 2) (v 0) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 3) (v 1), h.symm (v 2) (v 0)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 2)) (h.b_ne (v 1) (v 3)) (by ring)
  have pJK : ∀ v : Fin 4 → M, ∏ i, b (quatJ M v i) (quatK M v i) = 1 := by
    intro v
    rw [Fin.prod_univ_four]
    change b (-v 2) (-v 3) * b (v 3) (-v 2) * b (v 0) (v 1) * b (-v 1) (v 0) = 1
    simp only [h.b_neg_left, h.b_neg_right, inv_inv]
    rw [h.symm (v 3) (v 2), h.symm (v 1) (v 0)]
    exact eq_one_of_eq_inv_mul_self_mul_inv_mul_self (h.b_ne (v 0) (v 1)) (h.b_ne (v 2) (v 3)) (by ring)
  obtain ⟨a, c, d, e, habcd⟩ := Nat.sum_four_squares (Fintype.card (Fin 4 → M) ^ 2 - 1)
  have hN : 1 ≤ Fintype.card (Fin 4 → M) ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_pos (Fintype.card_pos_iff.mpr ⟨0⟩) 2).ne'
  obtain ⟨T, hTdef⟩ : ∃ T : (Fin 4 → M) →+ (Fin 4 → M), ∀ v,
      T v = a • v + c • quatI M v + d • quatJ M v + e • quatK M v :=
    ⟨AddMonoidHom.mk'
      (fun v : Fin 4 → M => a • v + c • quatI M v + d • quatJ M v + e • quatK M v)
      (fun v w => by simp only [map_add, smul_add]; abel), fun v => rfl⟩
  have hT : ∀ v : Fin 4 → M, (∏ i, φ (v i)) * (∏ i, φ (T v i)) = 1 := by
    intro v
    have hO : (∏ i, φ ((a • v + c • quatI M v + d • quatJ M v + e • quatK M v) i))
        = (∏ i, φ (v i)) ^ (a ^ 2) * (∏ i, φ (quatI M v i)) ^ (c ^ 2)
          * (∏ i, φ (quatJ M v i)) ^ (d ^ 2) * (∏ i, φ (quatK M v i)) ^ (e ^ 2) :=
      H.phi_orth4 v (quatI M v) (quatJ M v) (quatK M v)
        (pI v) (pJ v) (pK v) (pIJ v) (pIK v) (pJK v) a c d e
    have hsq : (∏ i, φ ((Fintype.card (Fin 4 → M) • v) i))
        = (∏ i, φ (v i)) ^ (Fintype.card (Fin 4 → M) ^ 2) := H.sq _ v
    rw [card_nsmul_eq_zero] at hsq
    simp only [Pi.zero_apply, h.phi_zero, Finset.prod_const_one] at hsq
    rw [hTdef, hO, hPI, hPJ, hPK, ← pow_add, ← pow_add, ← pow_add, habcd, ← pow_succ',
      Nat.sub_add_cancel hN, ← hsq]
  have key : (∑ v : Fin 4 → M, ∏ i, φ (v i)) ^ 2 = (Fintype.card (Fin 4 → M) : ℂ) :=
    H.sum_sq_of_anti T hT
  have hsum : (∑ x, φ x) ^ 4 = ∑ v : Fin 4 → M, ∏ i, φ (v i) := by
    calc (∑ x, φ x) ^ 4 = ∏ _i : Fin 4, ∑ x, φ x := by simp
      _ = ∑ v : Fin 4 → M, ∏ i, φ (v i) := by
        exact Fintype.prod_sum (fun _ x => φ x)
  rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hsum, key]
  simp
end Formalism.L2.Th1.H

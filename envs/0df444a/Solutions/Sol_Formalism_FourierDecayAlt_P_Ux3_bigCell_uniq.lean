-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.bigCell_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:07.359109+00:00
-- url     : https://prove2.me/submissions/687e73a3-4ae2-468e-9c98-13c791ccb0ec

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_eq_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_cancel_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_cancel_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_gv_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (x1 x1' x2 x2' : RC k j ρ) (Z1 Z2 : Matrix (Fin j) (Fin j) ℂ) (γ1 γ2 : B.Mat k ρ)
    (hZ1 : Z1.det ≠ 0) (hZ2 : Z2.det ≠ 0) (hγ2 : γ2 ∈ B.GV k ρ)
    (h : (Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1 * Rn k j ρ x1' = (Rn k j ρ x2)⁻¹ * mMap k j ρ Z2 γ2 * Rn k j ρ x2') :
    x1 = x2 ∧ x1' = x2' ∧ Z1 = Z2 ∧ γ1 = γ2 := by
  have key : Rn k j ρ x2 * (Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1 =
      mMap k j ρ Z2 γ2 * (Rn k j ρ x2' * (Rn k j ρ x1')⁻¹) := by
    calc Rn k j ρ x2 * (Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1
        = Rn k j ρ x2 * ((Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1 * Rn k j ρ x1') * (Rn k j ρ x1')⁻¹ := by
          simp only [Matrix.mul_assoc, rn_mul_inv, Matrix.mul_one]
      _ = Rn k j ρ x2 * ((Rn k j ρ x2)⁻¹ * mMap k j ρ Z2 γ2 * Rn k j ρ x2') * (Rn k j ρ x1')⁻¹ := by rw [h]
      _ = mMap k j ρ Z2 γ2 * (Rn k j ρ x2' * (Rn k j ρ x1')⁻¹) := by
          simp only [← Matrix.mul_assoc, rn_mul_inv, Matrix.one_mul]
  rw [rn_eq x2, rn_eq x1, uni_inv, rn_eq x2', rn_eq x1', uni_inv] at key
  unfold mMap at key
  rw [block3_mul, block3_mul, block3_mul, block3_mul, block3_eq_iff] at key
  obtain ⟨e11, -, -, e21, e22, e23, e31, -, e33⟩ := key
  simp at e11 e21 e22 e23 e31 e33
  have hW1 : IsUnit (G.wMat j * Z1).det := by
    rw [Matrix.det_mul]; exact (wMat_det j).mul (isUnit_iff_ne_zero.mpr hZ1)
  have hW2 : IsUnit (G.wMat j * Z2).det := by
    rw [Matrix.det_mul]; exact (wMat_det j).mul (isUnit_iff_ne_zero.mpr hZ2)
  have hZ : Z1 = Z2 := by
    have := congrArg (G.wMat j * ·) e31
    simpa [← Matrix.mul_assoc, wMat_mul_self] using this
  have hc : x1.1 = x2.1 := by
    have h0 := cancel_right _ _ hW1 e21
    have : -x1.1 + x2.1 = 0 := by
      ext i b; have := congrFun (congrFun h0 i) b; simpa using this
    rw [neg_add_eq_zero] at this; exact this
  have hc' : x1'.1 = x2'.1 := by
    have h0 := cancel_left _ _ (gv_det hγ2) e23.symm
    have : -x1'.1 + x2'.1 = 0 := by
      ext i b; have := congrFun (congrFun h0 i) b; simpa using this
    rw [neg_add_eq_zero] at this; exact this
  have hneg : ∀ y : Fin (2 * ρ + k + 1) → Fin j → ℂ, (Matrix.of (-y) : Matrix _ _ ℂ) = -Matrix.of y := fun y => rfl
  have hS : x1.2 = x2.2 := by
    have h0 := cancel_right _ _ hW1 e11
    rw [← hc, hneg] at h0
    have h1 : G.wMat j * (skewOf x2.2 - skewOf x1.2) = 0 := by
      rw [← h0]
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul]
      abel
    have h2 := cancel_left _ _ (wMat_det j) h1
    exact (skewOf_inj _ _ (sub_eq_zero.mp h2)).symm
  have hS' : x1'.2 = x2'.2 := by
    have h0 := cancel_left _ _ hW2 e33.symm
    rw [← hc', hneg] at h0
    have h1 : G.wMat j * (skewOf x2'.2 - skewOf x1'.2) = 0 := by
      rw [← h0]
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul]
      abel
    have h2 := cancel_left _ _ (wMat_det j) h1
    exact (skewOf_inj _ _ (sub_eq_zero.mp h2)).symm
  exact ⟨Prod.ext hc hS, Prod.ext hc' hS', hZ, e22⟩
end Formalism.FourierDecayAlt.P.Ux3

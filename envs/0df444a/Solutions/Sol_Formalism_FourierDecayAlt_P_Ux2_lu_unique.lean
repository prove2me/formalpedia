-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.lu_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:46.801999+00:00
-- url     : https://prove2.me/submissions/a9660ddc-004f-48a6-8381-7e3a308fdc22

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_uniK_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowK_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upK_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {L1 L2 U1 U2 : Matrix (Fin p) (Fin p) ℂ} (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (hL1 : uniK (kL p) L1) (hL2 : uniK (kL p) L2) (hU1 : uniK (kU p) U1) (hU2 : uniK (kU p) U2)
    (h : L1 * diagonal d * U1 = L2 * diagonal d * U2) : L1 = L2 ∧ U1 = U2 := by
  obtain ⟨hL2i, hL2a, hL2b⟩ := lowK_inv hL2
  obtain ⟨hU1i, hU1a, hU1b⟩ := upK_inv hU1
  have hYX : (L2⁻¹ * L1) * diagonal d = diagonal d * (U2 * U1⁻¹) := by
    have := congrArg (fun M => L2⁻¹ * M * U1⁻¹) h
    calc (L2⁻¹ * L1) * diagonal d = L2⁻¹ * (L1 * diagonal d * U1) * U1⁻¹ := by
          simp [Matrix.mul_assoc, hU1a]
      _ = L2⁻¹ * (L2 * diagonal d * U2) * U1⁻¹ := this
      _ = diagonal d * (U2 * U1⁻¹) := by simp [← Matrix.mul_assoc, hL2b]
  have hY := uniK_mul kL_inj hL2i hL1
  have hX := uniK_mul kU_inj hU2 hU1i
  have hY1 : L2⁻¹ * L1 = 1 := by
    ext a b
    have e := congrFun (congrFun hYX a) b
    rw [mul_diagonal, diagonal_mul] at e
    rcases lt_trichotomy a b with hab | hab | hab
    · rw [hY.2 a b (kL_lt.mpr hab), Matrix.one_apply_ne (ne_of_lt hab)]
    · subst hab; rw [hY.1, Matrix.one_apply_eq]
    · rw [hX.2 a b (kU_lt.mpr hab), mul_zero] at e
      rw [Matrix.one_apply_ne (ne_of_gt hab)]
      exact (mul_eq_zero.mp e).resolve_right (hd b)
  have hX1 : U2 * U1⁻¹ = 1 := by
    ext a b
    have e := congrFun (congrFun hYX a) b
    rw [mul_diagonal, diagonal_mul] at e
    rcases lt_trichotomy a b with hab | hab | hab
    · rw [hY.2 a b (kL_lt.mpr hab), zero_mul] at e
      rw [Matrix.one_apply_ne (ne_of_lt hab)]
      exact ((mul_eq_zero.mp e.symm).resolve_left (hd a))
    · subst hab; rw [hX.1, Matrix.one_apply_eq]
    · rw [hX.2 a b (kU_lt.mpr hab), Matrix.one_apply_ne (ne_of_gt hab)]
  constructor
  · calc L1 = (L2 * L2⁻¹) * L1 := by rw [hL2a, Matrix.one_mul]
      _ = L2 * (L2⁻¹ * L1) := Matrix.mul_assoc _ _ _
      _ = L2 := by rw [hY1, Matrix.mul_one]
  · symm
    calc U2 = U2 * (U1⁻¹ * U1) := by rw [hU1b, Matrix.mul_one]
      _ = (U2 * U1⁻¹) * U1 := (Matrix.mul_assoc _ _ _).symm
      _ = U1 := by rw [hX1, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Ux2

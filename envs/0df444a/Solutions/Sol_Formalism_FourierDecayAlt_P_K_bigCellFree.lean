-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.bigCellFree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:28.128386+00:00
-- url     : https://prove2.me/submissions/589534e8-4883-4e99-bac0-41e5b5f63fa3

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_upUni_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_upUni_isUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_upUni_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_lower_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_right_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.K
open Matrix Finset Real Formalism.FourierDecayAlt.K
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.K
theorem _root_.solution : BigCellFree := by
  intro K' _ m v v' u u' d hv hv' hu hu' hd h
  have hvU := upUni_isUnit hv
  have hv'U := upUni_isUnit hv'
  rw [Matrix.mul_assoc v (w0 m) (Matrix.diagonal d)] at h
  obtain ⟨W, hW⟩ : ∃ W, W = w0 m * Matrix.diagonal d := ⟨_, rfl⟩
  rw [← hW] at h
  have ha : IsUpUni (v⁻¹ * u * v) := upUni_mul (upUni_mul (upUni_inv hv) hu) hv
  have hc : IsUpUni (v' * u' * v'⁻¹) := upUni_mul (upUni_mul hv' hu') (upUni_inv hv')
  have hcU := upUni_isUnit hc
  have key : (v⁻¹ * u * v) * W * (v' * u' * v'⁻¹) = W := by
    have e : v⁻¹ * (u * (v * W * v') * u') * v'⁻¹ = W := by
      rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hvU, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hv'U, Matrix.mul_one]
    rw [show (v⁻¹ * u * v) * W * (v' * u' * v'⁻¹) = v⁻¹ * (u * (v * W * v') * u') * v'⁻¹ by
      simp only [Matrix.mul_assoc]]
    exact e
  have key2 : (v⁻¹ * u * v) * W = W * (v' * u' * v'⁻¹)⁻¹ := by
    calc (v⁻¹ * u * v) * W
        = (v⁻¹ * u * v) * W * ((v' * u' * v'⁻¹) * (v' * u' * v'⁻¹)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hcU, Matrix.mul_one]
      _ = ((v⁻¹ * u * v) * W * (v' * u' * v'⁻¹)) * (v' * u' * v'⁻¹)⁻¹ :=
          (Matrix.mul_assoc _ _ _).symm
      _ = W * (v' * u' * v'⁻¹)⁻¹ := by rw [key]
  have ha1 : v⁻¹ * u * v = 1 := lower_eq_one ha (upUni_inv hc) hd (by rw [← hW]; exact key2)
  rw [ha1, Matrix.one_mul] at key
  have hc1 : v' * u' * v'⁻¹ = 1 := right_eq_one hd (by rw [← hW]; exact key)
  constructor
  · calc u = v * (v⁻¹ * u * v) * v⁻¹ := by
          simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hvU, Matrix.one_mul]
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hvU, Matrix.mul_one]
      _ = 1 := by rw [ha1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hvU]
  · calc u' = v'⁻¹ * (v' * u' * v'⁻¹) * v' := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hv'U, Matrix.one_mul]
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hv'U, Matrix.mul_one]
      _ = 1 := by rw [hc1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hv'U]
end Formalism.FourierDecayAlt.P.K

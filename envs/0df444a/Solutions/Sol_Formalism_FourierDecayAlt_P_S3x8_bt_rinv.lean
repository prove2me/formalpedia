-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.bt_rinv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:34.919787+00:00
-- url     : https://prove2.me/submissions/88b512e8-71fc-4f64-b23a-c14a40cf22e3

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_one_block11
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_one_block21
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_one_block31
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_lcancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_uni_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {x y : Matrix (Idx r k) (Idx r k) A} (hx : BT x) (e : x * y = 1) : BT y := by
  obtain ⟨h11, h33, h21, h31, h32, h22⟩ := hx
  have y31 : b31 y = 0 := by
    have := block31_mul x y
    rw [e, one_block31, h31, h32] at this
    exact lcancel (uni_unit h33) (by simpa using this.symm)
  have y32 : b32 y = 0 := by
    have := block32_mul x y
    rw [e, block32_one, h31, h32] at this
    exact lcancel (uni_unit h33) (by simpa using this.symm)
  have y33 : b33 y = (b33 x)⁻¹ := by
    have := block33_mul x y
    rw [e, block33_one, h31, h32] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  have y21 : b21 y = 0 := by
    have := block21_mul x y
    rw [e, one_block21, h21, y31] at this
    exact lcancel h22 (by simpa using this.symm)
  have y22 : b22 y = (b22 x)⁻¹ := by
    have := block22_mul x y
    rw [e, block22_one, h21, y32] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  have y11 : b11 y = (b11 x)⁻¹ := by
    have := block11_mul x y
    rw [e, one_block11, y21, y31] at this
    exact (Matrix.inv_eq_right_inv (by simpa using this.symm)).symm
  exact ⟨y11 ▸ isUpUni_inv A h11, y33 ▸ isUpUni_inv A h33, y21, y31, y32,
    y22 ▸ Matrix.isUnit_nonsing_inv_det _ h22⟩
end Formalism.FourierDecayAlt.P.S3x8

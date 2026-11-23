-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.stabiliserTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:00.617398+00:00
-- url     : https://prove2.me/submissions/907d7931-b9ba-48ae-a96c-6560c85d79fe

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_det_of_cm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_ext9
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_one_block11
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block12_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block13_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_one_block21
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block23_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_one_block31
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_lcancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_rcancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_halfStab

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
variable {F : Type} [Field F] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution : StabiliserTrivial := by
  intro F _ r k g n n' hg hc hc' hn hn' e
  have g1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have g2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have e' : g⁻¹ * n = n' * g⁻¹ := by
    calc g⁻¹ * n = g⁻¹ * (n * g) * g⁻¹ := by simp only [mul_assoc, g1, mul_one]
      _ = g⁻¹ * (g * n') * g⁻¹ := by rw [e]
      _ = n' * g⁻¹ := by simp only [← mul_assoc, g2, one_mul]
  obtain ⟨a33, a11', a23, a12'⟩ := halfStab hc hn hn' e
  obtain ⟨a33', a11, a23', a12⟩ := halfStab hc' hn' hn e'
  have hd : IsUnit (b31 g).det := det_of_cm _ (hc r le_rfl).isUnit
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  obtain ⟨g11, g33, g22, g21, g31, g32⟩ := hn'
  have a13 : b13 n = 0 := by
    have e11 := congrArg b11 e
    rw [block11_mul, block11_mul, g21, g31, a11', a11, a12] at e11
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at e11
    refine rcancel hd ?_
    rw [Matrix.zero_mul]
    exact (left_eq_add.1 e11)
  have a13' : b13 n' = 0 := by
    have e33 := congrArg b33 e
    rw [block33_mul, block33_mul, h31, h32, a33', a33, a23'] at e33
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul] at e33
    refine lcancel hd ?_
    rw [Matrix.mul_zero]
    exact (add_eq_right.1 e33)
  constructor
  · apply ext9 <;> simp only [one_block11, block12_one, block13_one, one_block21, block22_one, block23_one, one_block31, block32_one,
      block33_one] <;> assumption
  · apply ext9 <;> simp only [one_block11, block12_one, block13_one, one_block21, block22_one, block23_one, one_block31, block32_one,
      block33_one] <;> assumption
end Formalism.FourierDecayAlt.P.S3x8

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.t_w0comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:42.386566+00:00
-- url     : https://prove2.me/submissions/6684598f-2565-4d00-b85f-17a1cc3a9764

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_weylMatrix_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mul_long_weyl_element_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution : WeylElementCommutesLevelOne := by
  intro k r' c g
  ext i j
  rw [weylMatrix_mul_apply, mul_long_weyl_element_apply, lev_out_row g (iL k r') j (Or.inr rfl), lev_out_row g (iZ k r') j (Or.inl rfl),
    lev_out_col g i (iL k r') (Or.inr rfl), lev_out_col g i (iZ k r') (Or.inl rfl)]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hj0 : j.val = 0 ∨ j.val = 2 * (1 + r') + k
  · rw [lev_out_col g i j hj0]
    simp only [iL, iZ, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
  · by_cases hi0 : i.val = 0 ∨ i.val = 2 * (1 + r') + k
    · rw [lev_out_row g i j hi0]
      simp only [iL, iZ, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
    · simp only [iL, iZ, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
end Formalism.FourierDecayAlt.P.LongWeylElement

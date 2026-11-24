-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.Hpk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:41.683482+00:00
-- url     : https://prove2.me/submissions/07f1f648-b5c4-48fe-abf6-644c96fcbbb1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_weylMatrix_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_col_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_Hpk_levPos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mm
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
theorem _root_.solution (k r' : ℕ) : Hpk k (1 + r') = w0 k r' 1 * ιLev k 1 r' (Hpk k r') := by
  ext i j
  rw [weylMatrix_mul_apply]
  simp only [star_one, inv_one, one_mul]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h0 : i.val = 0
  · rw [if_pos h0, lev_out_row (Hpk k r') (iL k r') j (Or.inr rfl)]
    simp only [Hpk, iL, Fin.ext_iff, Fin.val_mk, h0]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
  · by_cases hL : i.val = 2 * (1 + r') + k
    · rw [if_neg h0, if_pos hL, lev_out_row (Hpk k r') (iZ k r') j (Or.inl rfl)]
      simp only [Hpk, iZ, Fin.ext_iff, Fin.val_mk, hL]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
    · rw [if_neg h0, if_neg hL]
      have hmi : mid k r' i := by
        show 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
        omega
      by_cases hmj : mid k r' j
      · obtain ⟨s, rfl⟩ := (mid_iff k r' i).1 hmi
        obtain ⟨t, rfl⟩ := (mid_iff k r' j).1 hmj
        rw [lev_mm, Formalism.FourierDecayAlt.P.B2x4.Hpk_levPos]
      · rw [lev_col_n (Hpk k r') i j hmj, if_neg (fun h => by subst h; exact hmj hmi)]
        have hj' : ¬ (1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := hmj
        simp only [Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
end Formalism.FourierDecayAlt.P.LongWeylElement

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.up_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:52.752169+00:00
-- url     : https://prove2.me/submissions/899b2f3c-e95c-4ae2-bc01-a129d018f55f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_sub_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_es_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_mat_ext
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
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {u u' : Mx k r} (hu : u ∈ UP k r l) (hu' : u' ∈ UP k r l) (h : u *ᵥ 𝐬 = u' *ᵥ 𝐬) : u = u' := by
  apply mat_ext
  intro y
  have hy0 : ⟪y - ⟪y, 𝐞⟫ • 𝐬, 𝐞⟫ = 0 := by
    simp only [h_sub_left, h_smul_left, h_es_e, if_true]; ring
  obtain ⟨t, ht⟩ := hu.2.2 _ hy0
  obtain ⟨t', ht'⟩ := hu'.2.2 _ hy0
  have e1 := uh_herm hu.1.1 (y - ⟪y, 𝐞⟫ • 𝐬) 𝐬
  have e2 := uh_herm hu'.1.1 (y - ⟪y, 𝐞⟫ • 𝐬) 𝐬
  have e3 : ⟪𝐞, u' *ᵥ 𝐬⟫ = 1 := by
    conv_lhs => rw [← hu'.2.1]
    rw [uh_herm hu'.1.1, h_e_es, if_pos rfl]
  rw [ht, h, h_add_left, h_smul_left, e3] at e1
  rw [ht', h_add_left, h_smul_left, e3] at e2
  have htt : t = t' := by linear_combination e1 - e2
  have hy : y = (y - ⟪y, 𝐞⟫ • 𝐬) + ⟪y, 𝐞⟫ • 𝐬 := by simp
  rw [hy, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ht, ht', h, htt]
end Formalism.FourierDecayAlt.P.Qx4

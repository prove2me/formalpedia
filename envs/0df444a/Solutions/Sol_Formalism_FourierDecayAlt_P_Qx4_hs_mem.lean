-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.hs_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:14:06.68839+00:00
-- url     : https://prove2.me/submissions/de206bdb-5fdd-4b46-ab01-0d90877ee578

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_sub_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_sub_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_act
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_mem_UH_of
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
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (hH : Hᴴ = H) {p v : Fin n → ℂ} {σ : ℂ} (hpp : herm H p p = 0) (hvp : herm H v p = 0)
    (hσ : σ + conj σ + herm H v v = 0) : hs H p v σ ∈ UH H := by
  apply B2x8.mem_UH_of
  intro u w
  have hpv : herm H p v = 0 := by rw [← h_conj H hH, hvp, map_zero]
  have h1 : herm H p w = conj (herm H w p) := (h_conj H hH w p).symm
  have h2 : herm H v w = conj (herm H w v) := (h_conj H hH w v).symm
  rw [hs_act, hs_act]
  simp only [h_add_left, h_add_right, h_sub_left, h_sub_right, h_smul_left, h_smul_right, hpp, hvp, hpv, h1, h2]
  linear_combination (herm H u p * conj (herm H w p)) * hσ
end Formalism.FourierDecayAlt.P.Qx4

-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.wpL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:20:23.621403+00:00
-- url     : https://prove2.me/submissions/c8f569df-f696-4e23-bf18-9d6e0aee7a15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_z_mul_zi
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_uPow_neg_two
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_xS_cc
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution (hE : ExpSpec.{u}) [CharZero K] (W : WeierstrassCurve K) :
    ∃ M : K⟦X⟧, constantCoeff M = 1 ∧ wpL W = uPow (-2) * toL M := by
  obtain ⟨e0, e1, -⟩ := hE K W
  have hs : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' e0
  obtain ⟨E, hE'⟩ := X_dvd_iff.mpr e0
  have hE0 : constantCoeff E = 1 := by
    rw [hE'] at e1
    have := coeff_succ_X_mul 0 E
    rw [zero_add, e1] at this
    rw [← coeff_zero_eq_constantCoeff_apply, ← this]
  have hEi : E * E⁻¹ = 1 := PowerSeries.mul_inv_cancel E (by rw [hE0]; exact one_ne_zero)
  have hEi0 : constantCoeff E⁻¹ = 1 := by
    have := congrArg constantCoeff hEi
    rwa [map_mul, hE0, one_mul, map_one] at this
  have hinv : (toL (expSer W))⁻¹ = uPow (-1) * toL E⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [hE', map_mul]
    have := congrArg toL hEi
    rw [map_mul, map_one] at this
    linear_combination toL E * toL E⁻¹ * z_mul_zi (K := K) + this
  obtain ⟨T, hT⟩ : X ∣ xS W - 1 :=
    X_dvd_iff.mpr (by rw [map_sub, CurveSer.xS_cc, map_one, sub_self])
  have hT' : xS W = 1 + X * T := by linear_combination hT
  have hx0 : constantCoeff ((xS W).subst (expSer W)) = 1 := by
    rw [hT', ← coe_substAlgHom hs, map_add, map_one, map_mul, coe_substAlgHom, subst_X hs,
      map_add, map_one, map_mul, e0, zero_mul, add_zero]
  refine ⟨E⁻¹ ^ 2 * (xS W).subst (expSer W) + C (W.b₂ / 12) * X ^ 2, ?_, ?_⟩
  · rw [map_add, map_mul, map_pow, hEi0, hx0, map_mul, map_pow, constantCoeff_X]
    simp
  · rw [wpL, xZ, hinv, map_add, map_mul, map_mul, map_pow, map_pow, toL_C, uPow_neg_two]
    linear_combination
      (-HahnSeries.C (W.b₂ / 12) * (toL X * uPow (-1) + 1)) * z_mul_zi (K := K)
end Formalism.L2.Th1.A.WpSh

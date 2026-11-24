-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.wpL_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:05:27.944181+00:00
-- url     : https://prove2.me/submissions/f2f905dd-3089-4dce-8de0-b83f3ebf61bf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_add_eq_mul
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_derivative_X_mul
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_clearedM_of_ode
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_of_ode
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_wpL_eq
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
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
theorem _root_.solution (hE : ExpSpec.{u}) (hO : WpODE.{u}) [CharZero K] (W : WeierstrassCurve K) :
    wpL W = uPow (-2) + toL (wpReg W) ∧ Cleared (g₂ W) (g₃ W) (wpReg W) := by
  obtain ⟨M, hM1, hM⟩ := wpL_eq hE W
  have hode := (hO K W).2.1
  rw [hM] at hode
  have hC := clearedM_of_ode hode
  obtain ⟨M1, hM1'⟩ : X ∣ M - 1 := by
    rw [X_dvd_iff, map_sub, hM1, map_one, sub_self]
  have hMe : M = 1 + X * M1 := by
    rw [← hM1']
    ring
  rw [hMe] at hC
  unfold ClearedM at hC
  rw [map_add, Derivation.map_one_eq_zero, derivative_X_mul] at hC
  have key : X * (8 * M1 - X * (-4 * derivative K M1 - 11 * M1 ^ 2 - 2 * X * M1 * derivative K M1
      + X ^ 2 * derivative K M1 ^ 2 - 4 * X * M1 ^ 3 + C (g₂ W) * X ^ 2 * (1 + X * M1)
      + C (g₃ W) * X ^ 4)) = 0 := by
    linear_combination (-1 : K⟦X⟧) * hC
  have h8 := (mul_eq_zero.mp key).resolve_left X_ne_zero
  have hc : constantCoeff M1 = 0 := by
    have e := congrArg constantCoeff h8
    rw [map_sub, map_mul, map_mul, constantCoeff_X, zero_mul, sub_zero, map_ofNat, map_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  obtain ⟨M2, hM2⟩ : X ∣ M1 := X_dvd_iff.mpr hc
  have hL : wpL W = uPow (-2) + toL M2 := by
    rw [hM, hMe, hM2, show (1 : K⟦X⟧) + X * (X * M2) = 1 + X ^ 2 * M2 by ring, add_eq_mul]
  have hR : wpReg W = M2 := by
    ext n
    rw [wpReg, coeff_mk, hL]
    first
    | simp [uPow, HahnSeries.coeff_single, show (n : ℤ) ≠ -2 by omega]
    | simp [uPow, HahnSeries.single_coeff_of_ne, show (n : ℤ) ≠ -2 by omega]
    | simp [uPow, show (n : ℤ) ≠ -2 by omega]
  refine ⟨?_, ?_⟩
  · rw [hR]
    exact hL
  · rw [hR]
    apply cleared_of_ode
    rw [← hL]
    exact (hO K W).2.1
end Formalism.L2.Th1.A.WpSh

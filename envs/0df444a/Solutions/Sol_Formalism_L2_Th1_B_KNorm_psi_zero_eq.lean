-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.psi_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:26.517804+00:00
-- url     : https://prove2.me/submissions/368a5efc-ed22-4f82-9b8b-782dc9a89655

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nadd_lt
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_ndom
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_t4
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_tb4
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_psi_zero_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KNorm
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {b2 b4 b6 b8 x : K}
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ = 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 1 < ‖x‖) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) : ‖x‖ = 4 := by
  refine le_antisymm (psi_zero_le h2 hb2.le hb4 hb6 h0) ?_
  by_contra hlt
  push_neg at hlt
  have e1 : ‖x‖ ^ 3 / 4 < ‖x‖ ^ 2 := by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 2 := by nlinarith
  have e3 : 1 < ‖x‖ ^ 2 := by nlinarith
  have hd : ‖b2 * x ^ 2‖ = ‖x‖ ^ 2 := by rw [norm_mul, hb2, one_mul, norm_pow]
  have hr : ‖4 * x ^ 3 + 2 * b4 * x + b6‖ < ‖b2 * x ^ 2‖ := by
    rw [hd]
    exact nadd_lt (nadd_lt ((t4 h2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)
  have key := ndom hr
  rw [show b2 * x ^ 2 + (4 * x ^ 3 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring,
    h0, norm_zero, hd] at key
  nlinarith
end Formalism.L2.Th1.B.KNorm

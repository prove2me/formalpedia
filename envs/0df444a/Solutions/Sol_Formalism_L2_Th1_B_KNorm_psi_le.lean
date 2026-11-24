-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.psi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:08.35239+00:00
-- url     : https://prove2.me/submissions/6a69d963-7abf-4476-9731-175267cde7ee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nadd_le
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_t4
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_tb2
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_tb4

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
theorem _root_.solution (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ ‖x‖ ^ 3 / 4 := by
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have e1 : ‖x‖ ^ 2 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.2 hx)]
  have e2 : ‖x‖ / 2 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [mul_nonneg r0 (sub_nonneg.2 hx)]
  have e3 : 1 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hx 3]
  exact nadd_le (nadd_le (nadd_le (t4 h2 x).le ((tb2 hb2 x).trans e1)) ((tb4 h2 hb4 x).trans e2))
    (hb6.trans e3)
end Formalism.L2.Th1.B.KNorm

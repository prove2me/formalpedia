-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.four_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:05.67758+00:00
-- url     : https://prove2.me/submissions/ab2b6bd0-e14a-497f-bf2f-5bc6a428d588

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nadd_le
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
theorem _root_.solution (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : ‖x‖ = 4) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) :
    ‖4 * x + b2‖ ≤ 1 / 8 := by
  have e : x ^ 2 * (4 * x + b2) = -(2 * b4 * x + b6) := by linear_combination h0
  have hr : ‖2 * b4 * x + b6‖ ≤ 2 :=
    nadd_le ((tb4 h2 hb4 x).trans (by rw [hx]; norm_num)) (hb6.trans (by norm_num))
  have hm := congrArg norm e
  rw [norm_mul, norm_pow, hx, norm_neg] at hm
  nlinarith [norm_nonneg (4 * x + b2)]
end Formalism.L2.Th1.B.KNorm

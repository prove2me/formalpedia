-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.num_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:20.898811+00:00
-- url     : https://prove2.me/submissions/95e5dad1-8612-483d-b2f6-a1bb4de7daaa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nadd_lt
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_ndom
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
theorem _root_.solution (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1) (hb8 : ‖b8‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8‖ = ‖x‖ ^ 4 := by
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have r2 : 16 ≤ ‖x‖ ^ 2 := by nlinarith
  have r4 : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
  have e1 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  have e3 : 1 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  rw [show x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8 = x ^ 4 + -(b4 * x ^ 2 + 2 * b6 * x + b8) by ring]
  rw [ndom, norm_pow]
  rw [norm_neg, norm_pow]
  exact nadd_lt (nadd_lt ((tb2 hb4 x).trans_lt e1) ((tb4 h2 hb6 x).trans_lt e2)) (hb8.trans_lt e3)
end Formalism.L2.Th1.B.KNorm

-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.dup_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:06.476277+00:00
-- url     : https://prove2.me/submissions/977f164f-28d8-4d76-bd16-08bb106a1d3c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_psi_le
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_num_norm
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
    (hb8 : ‖b8‖ ≤ 1) (hx : 4 ≤ ‖x‖) {X : K}
    (hX : X * (4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
      = x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8) : 4 < ‖X‖ := by
  have hn := num_norm h2 hb4 hb6 hb8 hx
  have hp := psi_le h2 hb2 hb4 hb6 hx
  have hm := congrArg norm hX
  rw [norm_mul, hn] at hm
  by_contra hle
  push_neg at hle
  have hb : ‖X‖ * ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ 4 * (‖x‖ ^ 3 / 4) :=
    mul_le_mul hle hp (norm_nonneg _) (by norm_num)
  have r3 : 0 < ‖x‖ ^ 3 := pow_pos (by linarith) 3
  nlinarith
end Formalism.L2.Th1.B.KNorm

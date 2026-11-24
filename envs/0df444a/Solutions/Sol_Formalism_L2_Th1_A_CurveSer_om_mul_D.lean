-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.om_mul_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:29.301953+00:00
-- url     : https://prove2.me/submissions/4438a167-7bd6-43da-99c6-24695396ecda

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_mul_om
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_D_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.CurveSer
theorem _root_.solution (f : R⟦X⟧) : om W * D W f = derivative R f := by
  rw [D_apply, ← mul_assoc, mul_comm (om W), fw_mul_om W, one_mul]
end Formalism.L2.Th1.A.CurveSer

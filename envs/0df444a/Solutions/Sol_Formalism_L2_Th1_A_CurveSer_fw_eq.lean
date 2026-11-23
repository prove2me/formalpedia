-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.fw_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:39.369826+00:00
-- url     : https://prove2.me/submissions/d11f0602-4295-4fb7-a636-32533469dfbb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_eq

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
theorem _root_.solution : fw W = 1 - C W.a₁ * X - C W.a₂ * X ^ 2
    - X ^ 3 * (2 * C W.a₃ * wU W + 2 * C W.a₄ * X * wU W + 3 * C W.a₆ * wU W * wSer W) := by
  unfold fw
  linear_combination (-2 * C W.a₃ - 2 * C W.a₄ * X - 3 * C W.a₆ * wSer W) * wSer_eq W
end Formalism.L2.Th1.A.CurveSer

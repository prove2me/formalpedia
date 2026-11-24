-- Prove2me | solution 1 for Formalism.L2.Th1.E.Power.scaled_x_eq_off_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:44.196189+00:00
-- url     : https://prove2.me/submissions/6e68e811-c092-4cbd-9153-46732a349e11

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Power
namespace Formalism.L2.Th1.E.Power
theorem _root_.solution {K : Type} [Field K] (W : WeierstrassCurve K) (P : W.toAffine.Point) (hP : P ≠ 0) :
    x2 W P = X ^ 2 * xT W P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl
end Formalism.L2.Th1.E.Power

-- Prove2me | solution 1 for Formalism.L2.Th1.E.Power.sum_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:06.211859+00:00
-- url     : https://prove2.me/submissions/e036ec54-acd0-4a0d-85e0-6829a7f26d89

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
theorem _root_.solution {A : Type} [AddCommGroup A] [Fintype A] (M : A → ℝ) (Q : A) :
    ∑ P, M (P + Q) = ∑ P, M P :=
  Equiv.sum_comp (Equiv.addRight Q) M
end Formalism.L2.Th1.E.Power

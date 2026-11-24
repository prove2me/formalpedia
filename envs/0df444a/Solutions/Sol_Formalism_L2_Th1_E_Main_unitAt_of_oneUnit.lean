-- Prove2me | solution 1 for Formalism.L2.Th1.E.Main.unitAt_of_oneUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:42.015525+00:00
-- url     : https://prove2.me/submissions/7a4dc795-6476-4e70-bef1-f31ab63a440e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin

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
open Formalism.L2.Th1.E.Main
variable {K : Type} [NormedField K]
namespace Formalism.L2.Th1.E.Main
theorem _root_.solution {a : K} {V : K⟦X⟧} (ha : ‖a‖ = 1) (hV : OneUnit V) : UnitAt 0 (C a * V) :=
  ⟨a, V, ha, hV, by simp⟩
end Formalism.L2.Th1.E.Main

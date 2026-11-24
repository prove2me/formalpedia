-- Prove2me | solution 1 for Formalism.L2.Th1.E.Main.unitAt_C_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:01.457818+00:00
-- url     : https://prove2.me/submissions/c0b3d4eb-e24b-47ea-b25c-dadc25737f2b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin
import Theorems.Thm_Formalism_L2_Th1_E_Main_oneUnit_one

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
theorem _root_.solution {a : K} (ha : ‖a‖ = 1) : UnitAt 1 (C a * X : K⟦X⟧) :=
  ⟨a, 1, ha, oneUnit_one, by simp⟩
end Formalism.L2.Th1.E.Main

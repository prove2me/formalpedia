-- Prove2me | solution 1 for Formalism.L2.Th1.E.Main.unitAt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:42.936239+00:00
-- url     : https://prove2.me/submissions/69fa7958-f66e-40f3-80ed-fe9a6936cee0

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
theorem _root_.solution : UnitAt 0 (1 : K⟦X⟧) := ⟨1, 1, norm_one, oneUnit_one, by simp⟩
end Formalism.L2.Th1.E.Main

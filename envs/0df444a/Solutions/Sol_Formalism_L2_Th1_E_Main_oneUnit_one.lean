-- Prove2me | solution 1 for Formalism.L2.Th1.E.Main.oneUnit_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:10.235593+00:00
-- url     : https://prove2.me/submissions/1a33184b-8f48-4b18-b7de-42c09f0ec9d6

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
theorem _root_.solution : OneUnit (1 : K⟦X⟧) := by
  refine ⟨by simp, fun n => ?_⟩
  rw [coeff_one]
  split_ifs <;> simp
end Formalism.L2.Th1.E.Main

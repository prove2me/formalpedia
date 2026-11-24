-- Prove2me | solution 1 for Formalism.L2.Th1.E.root_integral_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:47.582654+00:00
-- url     : https://prove2.me/submissions/459de5b0-f7f9-4bcc-9cfc-33bcd93cfb25

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_rootInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
namespace Formalism.L2.Th1.E
theorem _root_.solution : RootInt := by
  intro K _ _ N g hN h0 hg
  exact Ser.rootInt hN h0 hg
end Formalism.L2.Th1.E

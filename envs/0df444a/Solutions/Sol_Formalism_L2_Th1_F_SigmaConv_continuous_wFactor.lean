-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaConv.continuous_wFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:03.022976+00:00
-- url     : https://prove2.me/submissions/b384641c-9c7c-4aae-a859-5979ef924d20

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaConv
namespace Formalism.L2.Th1.F.SigmaConv
theorem _root_.solution (l : ℂ) : Continuous (wFactor l) := by
  unfold wFactor
  fun_prop
end Formalism.L2.Th1.F.SigmaConv

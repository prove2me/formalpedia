-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaLog.differentiable_wFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:06.006927+00:00
-- url     : https://prove2.me/submissions/8476fe00-5b79-4128-b3b0-06dd3f8d2def

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog
import Theorems.Thm_Formalism_L2_Th1_F_SigmaLog_hasDerivAt_wFactor

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaLog
namespace Formalism.L2.Th1.F.SigmaLog
theorem _root_.solution (l : ℂ) : Differentiable ℂ (wFactor l) :=
  fun z => (hasDerivAt_wFactor l z).differentiableAt
end Formalism.L2.Th1.F.SigmaLog

-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenyPAux.analyticAt_PExcept
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:24:01.383411+00:00
-- url     : https://prove2.me/submissions/85bc7de6-2a01-4688-a44c-c77332b333d7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenyPAux
namespace Formalism.L2.Th1.F.IsogenyPAux
theorem _root_.solution (L : PeriodPair) (a z : ℂ) :
    AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 (a * (w - z))) z := by
  refine AnalyticAt.fun_comp (f := fun w : ℂ => a * (w - z)) (g := L.weierstrassPExcept 0) ?_
    (by fun_prop)
  simpa using L.analyticAt_weierstrassPExcept 0
end Formalism.L2.Th1.F.IsogenyPAux

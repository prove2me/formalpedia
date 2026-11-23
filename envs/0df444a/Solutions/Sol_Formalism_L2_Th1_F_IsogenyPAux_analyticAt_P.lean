-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenyPAux.analyticAt_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:56.780734+00:00
-- url     : https://prove2.me/submissions/9fa9c269-1f31-463f-a495-b4577f97d1ef

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
theorem _root_.solution (L : PeriodPair) (a b z : ℂ) (hz : a * z + b ∉ L.lattice) :
    AnalyticAt ℂ (fun w => L.weierstrassP (a * w + b)) z :=
  AnalyticAt.fun_comp (f := fun w : ℂ => a * w + b) (g := L.weierstrassP)
    (L.analyticOnNhd_weierstrassP _ hz) (by fun_prop)
end Formalism.L2.Th1.F.IsogenyPAux

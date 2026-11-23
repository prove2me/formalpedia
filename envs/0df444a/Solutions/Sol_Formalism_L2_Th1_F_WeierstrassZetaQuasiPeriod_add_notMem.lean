-- Prove2me | solution 1 for Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod.add_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:51.795808+00:00
-- url     : https://prove2.me/submissions/b8f7a772-0351-4450-a002-9dffc73c707f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ZetaQuasi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
namespace Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
theorem _root_.solution {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := fun h => hz (by simpa using sub_mem h hω)
end Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod

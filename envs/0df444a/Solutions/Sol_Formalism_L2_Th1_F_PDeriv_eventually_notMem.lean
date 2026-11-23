-- Prove2me | solution 1 for Formalism.L2.Th1.F.PDeriv.eventually_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:12.812454+00:00
-- url     : https://prove2.me/submissions/43bf00b5-81a3-4836-adcf-b013a823d843

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_PDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PDeriv
namespace Formalism.L2.Th1.F.PDeriv
theorem _root_.solution (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz
end Formalism.L2.Th1.F.PDeriv

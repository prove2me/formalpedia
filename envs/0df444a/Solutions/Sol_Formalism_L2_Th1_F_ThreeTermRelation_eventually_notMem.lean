-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.eventually_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:13.148003+00:00
-- url     : https://prove2.me/submissions/38048a1f-63c0-4044-b9ac-54e01d8fbcfb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero

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
open Formalism.L2.Th1.F.ThreeTermRelation
namespace Formalism.L2.Th1.F.ThreeTermRelation
theorem _root_.solution (L : PeriodPair) (z : ℂ) : ∀ᶠ x in 𝓝[≠] z, x ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds z)] with x hx0 hx1
  have hx0' : x ≠ z := hx0
  simp_all
end Formalism.L2.Th1.F.ThreeTermRelation

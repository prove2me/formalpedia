-- Prove2me | solution 1 for Formalism.L2.Th1.F.PDeriv.hasDerivAt_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:10.149326+00:00
-- url     : https://prove2.me/submissions/9e133432-8ea0-428d-9420-9b693ae29292

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
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hd := (L.differentiableOn_weierstrassP.differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  rwa [L.deriv_weierstrassP] at hd
end Formalism.L2.Th1.F.PDeriv

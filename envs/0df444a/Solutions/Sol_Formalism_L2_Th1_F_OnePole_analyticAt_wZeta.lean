-- Prove2me | solution 1 for Formalism.L2.Th1.F.OnePole.analyticAt_wZeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:45.380652+00:00
-- url     : https://prove2.me/submissions/dbe7d95a-daa5-4a5f-ab7f-8550595e2f70

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OnePole
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_differentiableOn_wZeta


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
open Formalism.L2.Th1.F.OnePole
open AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F.OnePole
theorem _root_.solution (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℂ (wZeta L) z := by
  exact (differentiableOn_wZeta L).analyticAt ((L.isClosed_lattice.isOpen_compl).mem_nhds hz)
end Formalism.L2.Th1.F.OnePole

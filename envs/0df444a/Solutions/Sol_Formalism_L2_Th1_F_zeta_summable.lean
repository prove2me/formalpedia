-- Prove2me | solution 1 for Formalism.L2.Th1.F.zeta_summable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:40.540612+00:00
-- url     : https://prove2.me/submissions/40422e7c-3183-4f73-b9bb-db90ab10ad85

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_hasSumLU_wZeta

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
open AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F
theorem _root_.solution : ZetaSummable := by
  intro L z
  exact (hasSumLU_wZeta L).hasSum.summable
end Formalism.L2.Th1.F

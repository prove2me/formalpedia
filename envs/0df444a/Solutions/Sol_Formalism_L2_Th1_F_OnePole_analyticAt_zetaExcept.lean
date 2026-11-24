-- Prove2me | solution 1 for Formalism.L2.Th1.F.OnePole.analyticAt_zetaExcept
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:58.248905+00:00
-- url     : https://prove2.me/submissions/9385588d-6e0b-49ad-aa00-08e39d5902df

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OnePole
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_differentiableOn_zetaExcept


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
theorem _root_.solution (L : PeriodPair) : AnalyticAt ℂ (zetaExcept L 0) 0 := by
  refine (differentiableOn_zetaExcept L 0).analyticAt ?_
  filter_upwards [eventually_nhdsWithin_iff.1 (eventually_notMem L 0 0)] with w hw
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_singleton_iff, SetLike.mem_coe, not_and, not_not]
  intro hmem
  by_contra hne
  exact hw hne (by simpa using hmem)
end Formalism.L2.Th1.F.OnePole

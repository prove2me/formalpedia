-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.analyticAt_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:43.129645+00:00
-- url     : https://prove2.me/submissions/baf2e378-3047-49b4-8241-78623a378307

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_dom_mem_nhds
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_hasDerivAt_v

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
open Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
namespace Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
theorem _root_.solution (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) : AnalyticAt ℂ (v L t) 0 :=
  DifferentiableOn.analyticAt
    (fun _ hz => (hasDerivAt_v L hz).differentiableAt.differentiableWithinAt) (dom_mem_nhds L ht)
end Formalism.L2.Th1.F.ThetaZeroTaylorLemmas

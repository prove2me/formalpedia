-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.ode_th
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:40:55.943547+00:00
-- url     : https://prove2.me/submissions/55da42d4-2a62-4fe4-b1d2-2eb2850f2d38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_dom_mem_nhds
import Theorems.Thm_Formalism_L2_Th1_F_th0LogDeriv


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
theorem _root_.solution (L : PeriodPair) {ω₀ : ℂ} (hω : ω₀ ∈ L.lattice) (ht : ω₀ / 2 ∉ L.lattice) :
    deriv (th0 L (ω₀ / 2)) =ᶠ[𝓝 0] fun z => v L (ω₀ / 2) z * th0 L (ω₀ / 2) z := by
  filter_upwards [dom_mem_nhds L ht] with z hz
  exact (th0LogDeriv L ω₀ z hω ht hz).deriv
end Formalism.L2.Th1.F.ThetaZeroTaylorLemmas

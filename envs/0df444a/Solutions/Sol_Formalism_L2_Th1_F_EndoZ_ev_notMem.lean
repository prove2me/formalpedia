-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.ev_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:23.64115+00:00
-- url     : https://prove2.me/submissions/0bf2d0f2-957a-4d95-b96c-6c1cae14ec1a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_PDeriv_eventually_notMem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_eventually_notMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
theorem _root_.solution (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  first
  | exact ThreeTermRelation.eventually_notMem L 0
  | exact Filter.inf_principal_eq_bot.1
      ((discreteTopology_subtype_iff.1 (inferInstanceAs (DiscreteTopology L.lattice))) 0
        L.lattice.zero_mem)
end Formalism.L2.Th1.F.EndoZ

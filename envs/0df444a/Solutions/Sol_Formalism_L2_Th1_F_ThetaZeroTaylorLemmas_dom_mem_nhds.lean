-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.dom_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:16.265278+00:00
-- url     : https://prove2.me/submissions/7854004f-c305-4a63-9963-2783b5cc0b97

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_isOpen_dom

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
theorem _root_.solution (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) :
    {z : ℂ | z + t ∉ L.lattice} ∈ 𝓝 (0 : ℂ) :=
  (isOpen_dom L t).mem_nhds (by simpa using ht)
end Formalism.L2.Th1.F.ThetaZeroTaylorLemmas

-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.ne_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:41:03.0774+00:00
-- url     : https://prove2.me/submissions/788cfeee-6ec3-45d8-9ea3-ad31635b31d9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance

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
theorem _root_.solution (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice) : w ≠ 0 := by
  rintro rfl
  exact hw L.lattice.zero_mem
end Formalism.L2.Th1.F.EndoZ

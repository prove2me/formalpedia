-- Prove2me | solution 1 for Formalism.L2.Th1.F.Iota.mk_padic_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:31:08.296032+00:00
-- url     : https://prove2.me/submissions/95166358-34fc-49cf-8228-f16ef529ad22

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MkLeOfDenseRange
import Theorems.Thm_Formalism_L2_Th1_F_Iota_mk_le_of_denseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Cardinal Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Iota
namespace Formalism.L2.Th1.F.Iota
theorem _root_.solution (l : ℕ) [Fact l.Prime] : #ℚ_[l] ≤ 𝔠 := by
  have := mk_le_of_denseRange _ (Padic.denseRange_ratCast l)
  simpa using this
end Formalism.L2.Th1.F.Iota

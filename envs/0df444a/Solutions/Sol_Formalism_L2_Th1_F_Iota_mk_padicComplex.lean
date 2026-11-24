-- Prove2me | solution 1 for Formalism.L2.Th1.F.Iota.mk_padicComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:24.522375+00:00
-- url     : https://prove2.me/submissions/95e5cd2c-bb0d-46c3-97eb-7de56e30d6ea

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MkLeOfDenseRange
import Theorems.Thm_Formalism_L2_Th1_F_Iota_mk_padicComplex_le

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] : #ℂ_[l] = 𝔠 :=
  le_antisymm (mk_padicComplex_le l) (continuum_le_cardinal_of_nontriviallyNormedField ℂ_[l])
end Formalism.L2.Th1.F.Iota

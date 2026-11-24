-- Prove2me | solution 1 for Formalism.L2.Th1.F.Iota.mk_padicAlgCl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:43:35.411195+00:00
-- url     : https://prove2.me/submissions/a87ca048-471f-4294-93ea-f37f52f145a9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MkLeOfDenseRange
import Theorems.Thm_Formalism_L2_Th1_F_Iota_mk_padic_le

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) ≤ 𝔠 :=
  (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
    (max_le (mk_padic_le l) aleph0_le_continuum)
end Formalism.L2.Th1.F.Iota

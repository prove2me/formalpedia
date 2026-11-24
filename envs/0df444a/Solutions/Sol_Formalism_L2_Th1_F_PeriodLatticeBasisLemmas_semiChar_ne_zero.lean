-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.semiChar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:25:01.793799+00:00
-- url     : https://prove2.me/submissions/7dd69227-8204-49f0-ae40-73ca40f7a61d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
theorem _root_.solution (L : PeriodPair) (ω : ℂ) : semiChar L ω ≠ 0 := by
  unfold Formalism.L2.Th1.F.semiChar
  split_ifs <;> norm_num
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas

-- Prove2me | solution 1 for Formalism.L2.Th1.E.ptOf_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:47.70511+00:00
-- url     : https://prove2.me/submissions/adb5c8cf-cd63-45c9-903f-3c0455ec57de

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
namespace Formalism.L2.Th1.E
theorem _root_.solution (t : ℂ) (ht : t ∈ L.lattice) : ptOf l L ι t = 0 := by
  unfold ptOf
  exact dif_neg (fun h => h.1 ht)
end Formalism.L2.Th1.E

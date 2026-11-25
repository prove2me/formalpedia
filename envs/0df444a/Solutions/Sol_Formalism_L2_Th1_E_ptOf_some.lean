-- Prove2me | solution 1 for Formalism.L2.Th1.E.ptOf_some
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:04:57.424152+00:00
-- url     : https://prove2.me/submissions/eae7a6c1-38b5-46e9-9c58-f48366804dc9

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
theorem _root_.solution (t : ℂ) (ht : t ∉ L.lattice) :
    ptOf l L ι t = .some _ _ (AddThm.nonsing l L ι t ht) := by
  unfold ptOf
  rw [dif_pos ⟨ht, AddThm.nonsing l L ι t ht⟩]
end Formalism.L2.Th1.E

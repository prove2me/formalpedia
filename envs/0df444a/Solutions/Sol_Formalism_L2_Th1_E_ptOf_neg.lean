-- Prove2me | solution 1 for Formalism.L2.Th1.E.ptOf_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:48.829355+00:00
-- url     : https://prove2.me/submissions/300b0458-eed2-4b12-977a-9228d4e74038

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Theorems.Thm_Formalism_L2_Th1_E_ptOf_some
import Theorems.Thm_Formalism_L2_Th1_E_ptOf_lattice

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
theorem _root_.solution (t : ℂ) : ptOf l L ι (-t) = -ptOf l L ι t := by
  by_cases ht : t ∈ L.lattice
  · rw [ptOf_lattice l L ι t ht, ptOf_lattice l L ι (-t) (L.lattice.neg_mem ht)]
    rfl
  · have ht' : -t ∉ L.lattice := fun h => ht (by simpa using L.lattice.neg_mem h)
    rw [ptOf_some l L ι t ht, ptOf_some l L ι (-t) ht', WeierstrassCurve.Affine.Point.neg_some]
    simp [L.weierstrassP_neg, L.derivWeierstrassP_neg, curveL, Formalism.L2.Th1.A.shortW,
      WeierstrassCurve.Affine.negY, neg_div]
end Formalism.L2.Th1.E

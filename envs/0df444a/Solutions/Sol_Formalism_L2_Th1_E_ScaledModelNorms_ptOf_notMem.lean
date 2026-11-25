-- Prove2me | solution 1 for Formalism.L2.Th1.E.ScaledModelNorms.ptOf_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:41.944266+00:00
-- url     : https://prove2.me/submissions/1a7a264f-5a0d-4003-850c-63c08d9ae945

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints

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
open Formalism.L2.Th1.E.ScaledModelNorms
open Formalism.L2.Th1
variable (l : ℕ) [Fact l.Prime]
variable (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
namespace Formalism.L2.Th1.E.ScaledModelNorms
theorem _root_.solution (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    ptOf l L ι t = .some _ _ (nonsing l L ι hΔ t ht) := by
  unfold ptOf
  rw [dif_pos ⟨ht, nonsing l L ι hΔ t ht⟩]
end Formalism.L2.Th1.E.ScaledModelNorms

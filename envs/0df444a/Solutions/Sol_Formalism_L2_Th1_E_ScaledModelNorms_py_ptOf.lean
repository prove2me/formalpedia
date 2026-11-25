-- Prove2me | solution 1 for Formalism.L2.Th1.E.ScaledModelNorms.py_ptOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:54.377106+00:00
-- url     : https://prove2.me/submissions/c9be489a-c17f-475d-8bd5-af3841085348

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
import Theorems.Thm_Formalism_L2_Th1_E_ScaledModelNorms_ptOf_notMem

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
    py (curveL l L ι) (ptOf l L ι t) = ι (L.derivWeierstrassP t) / 2 := by
  rw [ptOf_notMem l L ι hΔ t ht]
  rfl
end Formalism.L2.Th1.E.ScaledModelNorms

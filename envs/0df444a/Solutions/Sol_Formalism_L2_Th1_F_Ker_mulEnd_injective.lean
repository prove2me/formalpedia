-- Prove2me | solution 1 for Formalism.L2.Th1.F.Ker.mulEnd_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:25:01.535313+00:00
-- url     : https://prove2.me/submissions/8190dbd7-7b64-4011-a5b7-7b84e4a64d10

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Ker
namespace Formalism.L2.Th1.F.Ker
theorem _root_.solution (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (h : MulStable L α) :
    Function.Injective (mulEnd L α h) := by
  intro x y hxy
  have := congrArg Subtype.val hxy
  apply Subtype.ext
  simpa [mulEnd, hα] using this
end Formalism.L2.Th1.F.Ker

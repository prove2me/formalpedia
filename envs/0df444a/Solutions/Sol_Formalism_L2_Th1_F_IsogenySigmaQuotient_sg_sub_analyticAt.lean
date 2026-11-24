-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_sub_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:59.041173+00:00
-- url     : https://prove2.me/submissions/ecd76242-16c3-4998-aab6-229a6bf8b24a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (hb : SgStarBasic) (P z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => sgStar L (w - P)) z := by
  have hd := (hb L).1
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => sgStar L (w - P)).analyticAt z
end Formalism.L2.Th1.F.IsogenySigmaQuotient

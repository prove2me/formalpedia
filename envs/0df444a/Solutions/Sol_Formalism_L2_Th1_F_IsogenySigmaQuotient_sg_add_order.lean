-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_add_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:25:05.832337+00:00
-- url     : https://prove2.me/submissions/f7c7a1f3-2e39-41bc-a970-b04cdaee5bef

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_order

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
theorem _root_.solution (hord : SigmaOrder) (he : SigmaEntire) (P z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => sgStar L (w + P)) z = ind L (z + P) := by
  have := sg_order L hord he 1 P z one_ne_zero
  simp only [one_mul] at this
  exact this
end Formalism.L2.Th1.F.IsogenySigmaQuotient

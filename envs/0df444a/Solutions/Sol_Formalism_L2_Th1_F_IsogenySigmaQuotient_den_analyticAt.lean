-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.den_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:57.400612+00:00
-- url     : https://prove2.me/submissions/7ea10cc9-07ee-430f-8c37-621d548f5f9c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_fac_analyticAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)
private lemma analyticAt_prod_fac (hb : SgStarBasic) (T : Finset ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => ∏ P ∈ T, fac L P w) z := by
  refine Finset.induction_on T ?_ ?_
  · simp only [Finset.prod_empty]; exact analyticAt_const
  · intro a T ha ih
    have e : (fun w => ∏ P ∈ insert a T, fac L P w) = fun w => fac L a w * ∏ P ∈ T, fac L P w := by
      funext w; rw [Finset.prod_insert ha]
    rw [e]; exact (fac_analyticAt L hb a z).mul ih
end IsogenySigmaQuotient
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (hb : SgStarBasic) (z : ℂ) : AnalyticAt ℂ (den L α S) z := by
  have hd := (hb L).1
  have h1 : AnalyticAt ℂ (fun w => α ^ 2 * sgStar L w ^ 2) z :=
    (by fun_prop : Differentiable ℂ fun w => α ^ 2 * sgStar L w ^ 2).analyticAt z
  exact h1.mul (analyticAt_prod_fac L hb S z)
end Formalism.L2.Th1.F.IsogenySigmaQuotient

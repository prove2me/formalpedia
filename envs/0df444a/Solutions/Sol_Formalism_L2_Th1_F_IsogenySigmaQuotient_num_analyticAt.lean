-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.num_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:57.563513+00:00
-- url     : https://prove2.me/submissions/2d600422-0f7c-40ce-ba05-4922ac117d4b

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
theorem _root_.solution (hb : SgStarBasic) (z : ℂ) : AnalyticAt ℂ (num L α) z := by
  have hd := (hb L).1
  exact (show Differentiable ℂ (fun w => num L α w) by simp only [num]; fun_prop).analyticAt z
end Formalism.L2.Th1.F.IsogenySigmaQuotient

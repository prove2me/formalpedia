-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.fac_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:38.295854+00:00
-- url     : https://prove2.me/submissions/fedbc78c-bcf0-4337-b5bf-7b9be5703a5c

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
theorem _root_.solution (hb : SgStarBasic) (P z : ℂ) : AnalyticAt ℂ (fac L P) z := by
  have hd := (hb L).1
  exact (show Differentiable ℂ (fun w => fac L P w) by simp only [fac]; fun_prop).analyticAt z
end Formalism.L2.Th1.F.IsogenySigmaQuotient

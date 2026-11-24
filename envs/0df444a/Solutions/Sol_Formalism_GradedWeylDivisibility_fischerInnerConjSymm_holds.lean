-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fischerInnerConjSymm_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:54.281379+00:00
-- url     : https://prove2.me/submissions/a6d2569f-7326-4353-bf63-8535e2e6b295

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockHerm
import Theorems.Thm_Formalism_REAL_fischerInner_eq_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockHerm := by
  intro σ f g
  exact Formalism.REAL.fischerInner_eq_star g f
end Formalism.GradedWeylDivisibility

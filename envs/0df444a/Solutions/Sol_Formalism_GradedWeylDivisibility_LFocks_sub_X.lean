-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_sub_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:22.138716+00:00
-- url     : https://prove2.me/submissions/a34cdc81-1e02-4a67-bedb-948c52b7e0a1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {σ : Type*} [Fintype σ]
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (U : Matrix σ σ ℂ) (i : σ) :
    sub U (X i) = ∑ j, C (U i j) * X j := by
  unfold sub
  exact aeval_X _ _
end Formalism.GradedWeylDivisibility

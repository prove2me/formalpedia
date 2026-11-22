-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:04.642717+00:00
-- url     : https://prove2.me/submissions/be9db983-8aec-4551-98bd-44402b13a87e

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
theorem _root_.solution (U : Matrix σ σ ℂ) (a : ℂ) :
    sub U (C a) = C a := by
  unfold sub
  rw [aeval_C, algebraMap_eq]
end Formalism.GradedWeylDivisibility

-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.semistandard_index_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:05.881797+00:00
-- url     : https://prove2.me/submissions/2fdedfb6-51c9-4b29-ae86-ad812914eeee

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSIdxFinite
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_ssIdx_subset_Iic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : SSIdxFinite := by
  intro k n ν
  exact (Set.finite_Iic _).subset (ldbasis_ssIdx_subset_Iic k n ν)
end Formalism.GradedWeylDivisibility

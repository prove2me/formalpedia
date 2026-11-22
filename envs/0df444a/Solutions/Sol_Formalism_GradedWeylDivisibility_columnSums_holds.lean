-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.columnSums_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:51.845439+00:00
-- url     : https://prove2.me/submissions/ffc06462-2313-419f-8f10-0c3de41ec140

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_weight_colW_apply

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
theorem _root_.solution : ColSums := by
  intro R _ r n ν f hf m hm t
  have h1 := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [← lccomp_weight_colW_apply, h1 (mem_support_iff.mp hm)]
end Formalism.GradedWeylDivisibility

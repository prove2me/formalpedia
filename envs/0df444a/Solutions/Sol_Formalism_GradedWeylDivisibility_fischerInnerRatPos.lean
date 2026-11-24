-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fischerInnerRatPos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:08.8588+00:00
-- url     : https://prove2.me/submissions/f8173558-ed29-4049-bb19-35d625ad1ebc

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_self_pos
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_symm


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
theorem _root_.solution : FockQPos :=
  fun _ f g => ⟨lfockq_symm f g, fun hf => lfockq_self_pos f hf⟩
end Formalism.GradedWeylDivisibility
